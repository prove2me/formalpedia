-- Prove2me | solution 1 for DeferredInspection.SingleAgent.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T01:26:17.989007+00:00
-- url     : https://prove2.me/submissions/fc996008-1244-4e88-8f4f-0d9cdffebb61

import Mathlib
import Definitions.Def_DeferredInspection_SingleAgent_Model

open DeferredInspection.SingleAgent MeasureTheory Set Filter Topology

namespace DIL2

lemma clamp_cont : Continuous (fun t : ℝ => max 0 (min t 1)) :=
  continuous_const.max (continuous_id.min continuous_const)

lemma clamp_mem (t : ℝ) : max 0 (min t 1) ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

lemma clamp_eq {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : max 0 (min t 1) = t := by
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-! ### Continuity and stability of the optimal payment -/

lemma cands_bdd {y : ℝ → ℝ} (hy : IsAllocation y) {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) :
    BddBelow ((fun w => v * (y v - y w) + w) '' Icc 0 v) := by
  refine ⟨-v, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have h1 := hy v hv
  have h2 := hy w ⟨hw.1, hw.2.trans hv.2⟩
  simp only [mem_Icc] at h1 h2
  nlinarith [hv.1, hw.1]

lemma optPay_contOn {y : ℝ → ℝ} (hc : ContinuousOn y (Icc 0 1)) :
    ContinuousOn (optPay y) (Icc 0 1) := by
  set yt := fun t => y (max 0 (min t 1)) with hyt
  have hytc : Continuous yt := hc.comp_continuous clamp_cont clamp_mem
  set g : ℝ → ℝ → ℝ := fun v t => v * (yt v - yt (t * v)) + t * v with hg
  have hgc : Continuous (Function.uncurry g) := by
    simp only [hg, Function.uncurry]
    fun_prop
  have hh : Continuous fun v => sInf (g v '' Icc 0 1) := isCompact_Icc.continuous_sInf hgc
  refine hh.continuousOn.congr ?_
  intro v hv
  unfold optPay
  congr 1
  ext c
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwI : w ∈ Icc (0:ℝ) 1 := ⟨hw.1, hw.2.trans hv.2⟩
    rcases hv.1.lt_or_eq with hv0 | hv0
    · refine ⟨w / v, ⟨div_nonneg hw.1 hv0.le, (div_le_one hv0).2 hw.2⟩, ?_⟩
      simp only [hg, hyt]
      rw [div_mul_cancel₀ _ hv0.ne', clamp_eq hv, clamp_eq hwI]
    · subst hv0
      have : w = 0 := le_antisymm hw.2 hw.1
      subst this
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [hg]⟩
  · rintro ⟨t, ht, rfl⟩
    have htv : t * v ∈ Icc 0 v := ⟨mul_nonneg ht.1 hv.1, by nlinarith [ht.2, hv.1]⟩
    refine ⟨t * v, htv, ?_⟩
    simp only [hg, hyt]
    rw [clamp_eq hv, clamp_eq ⟨htv.1, htv.2.trans hv.2⟩]

lemma optPay_close {y z : ℝ → ℝ} (hy : IsAllocation y) (hz : IsAllocation z) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ v ∈ Icc (0:ℝ) 1, |y v - z v| ≤ ε) {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) :
    optPay y v - 2 * ε ≤ optPay z v := by
  unfold optPay
  apply le_csInf ((nonempty_Icc.2 hv.1).image _)
  rintro _ ⟨w, hw, rfl⟩
  have hwI : w ∈ Icc (0:ℝ) 1 := ⟨hw.1, hw.2.trans hv.2⟩
  have h1 := csInf_le (cands_bdd hy hv) ⟨w, hw, rfl⟩
  have e1 := abs_le.1 (h v hv)
  have e2 := abs_le.1 (h w hwI)
  simp only at h1 ⊢
  nlinarith [hv.1, hv.2]

lemma revenue_close (f : ℝ → ℝ) (hfc : ContinuousOn f (Icc 0 1)) {C : ℝ}
    (hC : ∀ v ∈ Icc (0:ℝ) 1, |f v| ≤ C) {y z : ℝ → ℝ} (hy : IsAllocation y) (hz : IsAllocation z)
    (hyc : ContinuousOn y (Icc 0 1)) (hzc : ContinuousOn z (Icc 0 1)) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ v ∈ Icc (0:ℝ) 1, |y v - z v| ≤ ε) :
    |allocRevenue f y - allocRevenue f z| ≤ 2 * ε * C := by
  unfold allocRevenue
  have iy : IntervalIntegrable (fun v => optPay y v * f v) volume 0 1 :=
    ((optPay_contOn hyc).mul hfc).intervalIntegrable_of_Icc zero_le_one
  have iz : IntervalIntegrable (fun v => optPay z v * f v) volume 0 1 :=
    ((optPay_contOn hzc).mul hfc).intervalIntegrable_of_Icc zero_le_one
  rw [← intervalIntegral.integral_sub iy iz]
  have h' : ∀ v ∈ Icc (0:ℝ) 1, |z v - y v| ≤ ε := fun v hv => by rw [abs_sub_comm]; exact h v hv
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := 2 * ε * C)
    (f := fun v => optPay y v * f v - optPay z v * f v) (by
      intro v hv
      rw [uIoc_of_le zero_le_one] at hv
      have hvI : v ∈ Icc (0:ℝ) 1 := ⟨hv.1.le, hv.2⟩
      have a1 := optPay_close hy hz hε h hvI
      have a2 := optPay_close hz hy hε h' hvI
      have hd : |optPay y v - optPay z v| ≤ 2 * ε := abs_le.2 ⟨by linarith, by linarith⟩
      rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
      exact mul_le_mul hd (hC v hvI) (abs_nonneg _) (by linarith))
  simpa [Real.norm_eq_abs] using this

/-! ### The smoothing -/

section Smooth
variable {x : ℝ → ℝ} (hx : IsAllocation x) (hc : ContinuousOn x (Icc 0 1))
  (hcv : ConcaveOn ℝ (Icc 0 1) x)

/-- Sliding average of the clamped allocation over a window of length `δ`. -/
noncomputable def avg (x : ℝ → ℝ) (δ v : ℝ) : ℝ :=
  (1 / δ) * ∫ s in (0:ℝ)..δ, x (max 0 (min ((1 - δ) * v + s) 1))

include hc in
lemma xt_cont : Continuous (fun t => x (max 0 (min t 1))) :=
  hc.comp_continuous clamp_cont clamp_mem

lemma window_mem {δ v s : ℝ} (hδ1 : δ ≤ 1) (hv : v ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc 0 δ) :
    (1 - δ) * v + s ∈ Icc (0:ℝ) 1 :=
  ⟨by nlinarith [hv.1, hs.1], by nlinarith [hv.2, hs.2, hv.1]⟩

include hx hc in
lemma avg_mem {δ : ℝ} (hδ : 0 < δ) (v : ℝ) : avg x δ v ∈ Icc (0:ℝ) 1 := by
  have hint : IntervalIntegrable (fun s => x (max 0 (min ((1 - δ) * v + s) 1))) volume 0 δ :=
    ((xt_cont hc).comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have h0 : 0 ≤ ∫ s in (0:ℝ)..δ, x (max 0 (min ((1 - δ) * v + s) 1)) :=
    intervalIntegral.integral_nonneg hδ.le (fun s _ => (hx _ (clamp_mem _)).1)
  have h1 : ∫ s in (0:ℝ)..δ, x (max 0 (min ((1 - δ) * v + s) 1)) ≤ ∫ s in (0:ℝ)..δ, (1:ℝ) :=
    intervalIntegral.integral_mono_on hδ.le hint intervalIntegrable_const
      (fun s _ => (hx _ (clamp_mem _)).2)
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at h1
  unfold avg
  constructor
  · positivity
  · rw [one_div, inv_mul_le_iff₀ hδ, mul_one]; exact h1

include hc hcv in
lemma avg_concave {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : ConcaveOn ℝ (Icc 0 1) (avg x δ) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro a ha b hb α β hα hβ hαβ
  have hct := xt_cont hc
  have ia : IntervalIntegrable (fun s => x (max 0 (min ((1 - δ) * a + s) 1))) volume 0 δ :=
    (hct.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have ib : IntervalIntegrable (fun s => x (max 0 (min ((1 - δ) * b + s) 1))) volume 0 δ :=
    (hct.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have iab : IntervalIntegrable
      (fun s => x (max 0 (min ((1 - δ) * (α * a + β * b) + s) 1))) volume 0 δ :=
    (hct.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have key : ∫ s in (0:ℝ)..δ, (α * x (max 0 (min ((1 - δ) * a + s) 1)) +
      β * x (max 0 (min ((1 - δ) * b + s) 1))) ≤
      ∫ s in (0:ℝ)..δ, x (max 0 (min ((1 - δ) * (α * a + β * b) + s) 1)) := by
    apply intervalIntegral.integral_mono_on hδ.le ((ia.const_mul α).add (ib.const_mul β)) iab
    intro s hs
    have pa := window_mem hδ1 ha hs
    have pb := window_mem hδ1 hb hs
    have hab : α * a + β * b ∈ Icc (0:ℝ) 1 := by
      have := (convex_Icc (0:ℝ) 1) ha hb hα hβ hαβ
      simpa [smul_eq_mul] using this
    have pab := window_mem hδ1 hab hs
    rw [clamp_eq pa, clamp_eq pb, clamp_eq pab]
    have := hcv.2 pa pb hα hβ hαβ
    simp only [smul_eq_mul] at this
    have e : α * ((1 - δ) * a + s) + β * ((1 - δ) * b + s) = (1 - δ) * (α * a + β * b) + s := by
      have : β = 1 - α := by linarith
      subst this; ring
    rw [e] at this
    exact this
  rw [intervalIntegral.integral_add (ia.const_mul α) (ib.const_mul β),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at key
  unfold avg
  simp only [smul_eq_mul]
  have hd : 0 ≤ 1 / δ := by positivity
  have := mul_le_mul_of_nonneg_left key hd
  nlinarith

include hc in
lemma avg_differentiable {δ : ℝ} : Differentiable ℝ (avg x δ) := by
  set xt := fun t => x (max 0 (min t 1)) with hxt
  have hct : Continuous xt := xt_cont hc
  set F := fun u => ∫ t in (0:ℝ)..u, xt t with hF
  have hFd : Differentiable ℝ F := fun u => (hct.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt
  have heq : avg x δ = fun v => (1 / δ) * (F ((1 - δ) * v + δ) - F ((1 - δ) * v)) := by
    funext v
    unfold avg
    congr 1
    have h1 := intervalIntegral.integral_comp_add_left (a := 0) (b := δ) xt ((1 - δ) * v)
    simp only [hxt, add_zero] at h1
    rw [h1]
    simp only [hF]
    rw [intervalIntegral.integral_interval_sub_left (hct.intervalIntegrable _ _)
      (hct.intervalIntegrable _ _)]
  rw [heq]
  intro v
  have h1 : DifferentiableAt ℝ (fun v => F ((1 - δ) * v + δ)) v :=
    (hFd _).comp v ((differentiableAt_id.const_mul _).add_const _)
  have h2 : DifferentiableAt ℝ (fun v => F ((1 - δ) * v)) v :=
    (hFd _).comp v (differentiableAt_id.const_mul _)
  exact (h1.sub h2).const_mul _

include hc in
lemma avg_close {ε η : ℝ} (hη : ∀ a ∈ Icc (0:ℝ) 1, ∀ b ∈ Icc (0:ℝ) 1, dist a b < η → dist (x a) (x b) < ε)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδη : δ < η) {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) :
    |avg x δ v - x v| ≤ ε := by
  have hct := xt_cont hc
  have iw : IntervalIntegrable (fun s => x (max 0 (min ((1 - δ) * v + s) 1))) volume 0 δ :=
    (hct.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hrepr : avg x δ v - x v =
      (1 / δ) * ∫ s in (0:ℝ)..δ, (x (max 0 (min ((1 - δ) * v + s) 1)) - x v) := by
    rw [intervalIntegral.integral_sub iw intervalIntegrable_const, intervalIntegral.integral_const]
    unfold avg
    simp only [smul_eq_mul, sub_zero]
    field_simp
  rw [hrepr]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ) (C := ε)
    (f := fun s => x (max 0 (min ((1 - δ) * v + s) 1)) - x v) (by
      intro s hs
      rw [uIoc_of_le hδ.le] at hs
      have hsI : s ∈ Icc 0 δ := ⟨hs.1.le, hs.2⟩
      have pw := window_mem hδ1 hv hsI
      rw [clamp_eq pw, Real.norm_eq_abs, ← Real.dist_eq]
      apply le_of_lt
      apply hη _ pw _ hv
      rw [Real.dist_eq]
      have : (1 - δ) * v + s - v = s - δ * v := by ring
      rw [this, abs_lt]
      constructor <;> nlinarith [hs.1, hs.2, hv.1, hv.2])
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hδ] at hb
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / δ)]
  calc 1 / δ * |∫ s in (0:ℝ)..δ, (x (max 0 (min ((1 - δ) * v + s) 1)) - x v)|
      ≤ 1 / δ * (ε * δ) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ε := by field_simp

end Smooth

/-- The strictly concave perturbation. -/
def q (v : ℝ) : ℝ := 2 * v - v ^ 2

lemma q_mem {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : q v ∈ Icc (0:ℝ) 1 := by
  unfold q; constructor <;> nlinarith [hv.1, hv.2]

lemma q_strict {a b α β : ℝ} (hab : a ≠ b) (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β = 1) :
    α * q a + β * q b < q (α * a + β * b) := by
  have e : q (α * a + β * b) - (α * q a + β * q b) = α * β * (a - b) ^ 2 := by
    have : β = 1 - α := by linarith
    subst this; unfold q; ring
  have : 0 < α * β * (a - b) ^ 2 := by
    have : 0 < (a - b) ^ 2 := by
      have : a - b ≠ 0 := sub_ne_zero.2 hab
      positivity
    positivity
  linarith

/-- The approximating sequence. -/
noncomputable def xs (x : ℝ → ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  (1 - 1 / ((n:ℝ) + 2)) * avg x (1 / ((n:ℝ) + 2)) v + 1 / ((n:ℝ) + 2) * q v

lemma dpos (n : ℕ) : 0 < 1 / ((n:ℝ) + 2) := by positivity
lemma dle (n : ℕ) : 1 / ((n:ℝ) + 2) ≤ 1 / 2 := by
  apply one_div_le_one_div_of_le (by norm_num); linarith [n.cast_nonneg (α := ℝ)]

end DIL2

open DIL2 in
theorem solution (f : ℝ → ℝ) (hf : DeferredInspection.SingleAgent.Assumption1 f) (x : ℝ → ℝ)
    (hx : DeferredInspection.SingleAgent.IsAllocation x) (hc : ContinuousOn x (Icc 0 1))
    (hcv : ConcaveOn ℝ (Icc 0 1) x) :
    ∃ (xs : ℕ → ℝ → ℝ) (vh : ℕ → ℝ),
      (∀ k, DeferredInspection.SingleAgent.IsAllocation (xs k) ∧ vh k ∈ Icc (0 : ℝ) 1 ∧
        StrictConcaveOn ℝ (Icc 0 (vh k)) (xs k) ∧
        DifferentiableOn ℝ (xs k) (Icc 0 (vh k)) ∧
        ∀ v ∈ Ioc (vh k) 1, xs k v = 1) ∧
      TendstoUniformlyOn xs x atTop (Icc 0 1) ∧
      Tendsto (fun k => DeferredInspection.SingleAgent.allocRevenue f (xs k)) atTop
        (𝓝 (DeferredInspection.SingleAgent.allocRevenue f x)) := by
  -- basic properties of each term
  have hmem : ∀ n, IsAllocation (DIL2.xs x n) := by
    intro n v hv
    have hd := dpos n
    have hd2 := dle n
    have h1 := avg_mem hx hc hd v
    have h2 := q_mem hv
    unfold DIL2.xs
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hcont : ∀ n, ContinuousOn (DIL2.xs x n) (Icc 0 1) := by
    intro n
    have := (avg_differentiable hc (δ := 1 / ((n:ℝ) + 2))).continuous
    unfold DIL2.xs q
    exact (continuous_const.mul this |>.add (continuous_const.mul (by fun_prop))).continuousOn
  -- uniform closeness
  have hunif : UniformContinuousOn x (Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc
  have hclose : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc (0:ℝ) 1, |DIL2.xs x n v - x v| < ε := by
    intro ε hε
    obtain ⟨η, hη, hηp⟩ := Metric.uniformContinuousOn_iff.1 hunif (ε / 2) (by linarith)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min hη (by linarith : (0:ℝ) < ε / 2))
    refine ⟨N, fun n hn v hv => ?_⟩
    set δ := 1 / ((n:ℝ) + 2) with hδ
    have hd := dpos n
    have hd2 := dle n
    have hδN : δ < min η (ε / 2) := by
      refine lt_of_le_of_lt ?_ hN
      apply one_div_le_one_div_of_le (by positivity)
      have : (N:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hA := avg_close hc hηp hd (by linarith) (lt_of_lt_of_le hδN (min_le_left _ _)) hv
    have hq := q_mem hv
    have hxv := hx v hv
    have e : DIL2.xs x n v - x v = (1 - δ) * (avg x δ v - x v) + δ * (q v - x v) := by
      unfold DIL2.xs; ring
    rw [e]
    have hδε : δ < ε / 2 := lt_of_lt_of_le hδN (min_le_right _ _)
    have t1 : |(1 - δ) * (avg x δ v - x v)| ≤ ε / 2 := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      nlinarith [abs_nonneg (avg x δ v - x v)]
    have t2 : |δ * (q v - x v)| ≤ δ := by
      rw [abs_mul, abs_of_pos hd]
      have : |q v - x v| ≤ 1 := abs_le.2 ⟨by linarith [hq.1, hxv.2], by linarith [hq.2, hxv.1]⟩
      nlinarith
    calc |(1 - δ) * (avg x δ v - x v) + δ * (q v - x v)|
        ≤ |(1 - δ) * (avg x δ v - x v)| + |δ * (q v - x v)| := abs_add_le _ _
      _ < ε := by linarith
  refine ⟨DIL2.xs x, fun _ => 1, ?_, ?_, ?_⟩
  · intro n
    have hd := dpos n
    have hd2 := dle n
    refine ⟨hmem n, ⟨zero_le_one, le_rfl⟩, ?_, ?_, ?_⟩
    · refine ⟨convex_Icc 0 1, ?_⟩
      intro a ha b hb hab α β hα hβ hαβ
      have hA := (avg_concave hc hcv hd (by linarith)).2 ha hb hα.le hβ.le hαβ
      have hQ := q_strict hab hα hβ hαβ
      simp only [smul_eq_mul] at hA ⊢
      unfold DIL2.xs
      have h1 : 0 ≤ 1 - 1 / ((n:ℝ) + 2) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hA h1, mul_lt_mul_of_pos_left hQ hd]
    · have := (avg_differentiable hc (δ := 1 / ((n:ℝ) + 2)))
      unfold DIL2.xs q
      exact ((this.const_mul _).add ((by fun_prop : Differentiable ℝ fun v : ℝ => 2 * v - v ^ 2).const_mul _)).differentiableOn
    · intro v hv; exact absurd hv.2 (not_le.2 hv.1)
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hclose ε hε
    filter_upwards [eventually_ge_atTop N] with n hn v hv
    rw [Real.dist_eq, abs_sub_comm]
    exact hN n hn v hv
  · -- revenue convergence
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.1.continuousOn
    have hC' : ∀ v ∈ Icc (0:ℝ) 1, |f v| ≤ |C| + 1 := fun v hv => by
      have := hC v hv; rw [Real.norm_eq_abs] at this; linarith [le_abs_self C]
    rw [Metric.tendsto_atTop]
    intro ε hε
    set K := |C| + 1 with hK
    have hKpos : 0 < K := by positivity
    obtain ⟨N, hN⟩ := hclose (ε / (4 * K)) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have := revenue_close f hf.1.continuousOn hC' (hmem n) hx (hcont n) hc
      (ε := ε / (4 * K)) (by positivity) (fun v hv => (hN n hn v hv).le)
    have e : 2 * (ε / (4 * K)) * K = ε / 2 := by field_simp; ring
    rw [e] at this
    linarith
