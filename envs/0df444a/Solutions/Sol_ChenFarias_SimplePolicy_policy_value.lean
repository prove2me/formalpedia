-- Prove2me | solution 1 for ChenFarias.SimplePolicy.policy_value
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T19:00:33.129798+00:00
-- url     : https://prove2.me/submissions/e89b0ec8-3378-419d-aa91-7069e02da330

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open ChenFarias.SimplePolicy

lemma cf_lintegral_expMeasure (β : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ s, g s ∂expMeasure β =
      ∫⁻ s in Ici 0, ENNReal.ofReal (β * Real.exp (-(β * s))) * g s := by
  have hpdf : Measurable (exponentialPDF β) :=
    (measurable_exponentialPDFReal β).ennreal_ofReal
  have : expMeasure β = volume.withDensity (exponentialPDF β) := rfl
  rw [this, lintegral_withDensity_eq_lintegral_mul _ hpdf hg]
  have hind : (exponentialPDF β * g) =
      (Ici (0:ℝ)).indicator (fun s => ENNReal.ofReal (β * Real.exp (-(β * s))) * g s) := by
    funext s
    by_cases hs : 0 ≤ s
    · simp [Set.indicator_of_mem (show s ∈ Ici (0:ℝ) from hs), exponentialPDF_of_nonneg hs]
    · push Not at hs
      simp [Set.indicator_of_notMem (show s ∉ Ici (0:ℝ) from not_le.2 hs),
        exponentialPDF_of_neg hs]
  rw [hind, lintegral_indicator measurableSet_Ici]

lemma cf_lintegral_Ioi_FTC {g g' : ℝ → ℝ} {a l : ℝ}
    (hderiv : ∀ x ∈ Ici a, HasDerivAt g (g' x) x) (hpos : ∀ x ∈ Ioi a, 0 ≤ g' x)
    (hg : Tendsto g atTop (𝓝 l)) :
    ∫⁻ x in Ioi a, ENNReal.ofReal (g' x) = ENNReal.ofReal (l - g a) := by
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hg
  rw [← integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hg,
    ofReal_integral_eq_lintegral_ofReal hint]
  exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpos)

lemma cf_expMeasure_Iio (r : ℝ) : expMeasure r (Iio 0) = 0 := by
  have : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  rw [this, withDensity_apply _ measurableSet_Iio]
  rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
    (fun x hx => exponentialPDF_of_neg hx)]
  simp

/-- Tail of the exponential law. -/
lemma cf_expMeasure_Ici (β a : ℝ) (hβ : 0 < β) (ha : 0 ≤ a) :
    expMeasure β (Ici a) = ENNReal.ofReal (Real.exp (-(β * a))) := by
  rw [← lintegral_indicator_one measurableSet_Ici,
    cf_lintegral_expMeasure β (g := (Ici a).indicator 1)
      ((measurable_const).indicator measurableSet_Ici)]
  have h1 : (fun s => ENNReal.ofReal (β * Real.exp (-(β * s))) * (Ici a).indicator 1 s) =
      (Ici a).indicator (fun s => ENNReal.ofReal (β * Real.exp (-(β * s)))) := by
    funext s
    by_cases hs : s ∈ Ici a
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  rw [h1, lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    show Ici a ∩ Ici (0:ℝ) = Ici a from inter_eq_left.2 (Ici_subset_Ici.2 ha),
    ← setLIntegral_congr Ioi_ae_eq_Ici]
  have hderiv : ∀ x ∈ Ici a, HasDerivAt (fun s => -Real.exp (-(β * s)))
      (β * Real.exp (-(β * x))) x := by
    intro x _
    have := (((hasDerivAt_id x).const_mul β).neg.exp).neg
    refine this.congr_deriv ?_
    simp only [Pi.neg_apply, id, mul_one]; ring
  have hpos : ∀ x ∈ Ioi a, 0 ≤ β * Real.exp (-(β * x)) := fun x _ => by positivity
  have htend : Tendsto (fun s => -Real.exp (-(β * s))) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hβ)
    simpa [Function.comp_def] using this.neg
  rw [cf_lintegral_Ioi_FTC hderiv hpos htend]
  congr 1; ring

lemma cf_clock_ae_nonneg (x0 : ℕ) : ∀ᵐ e ∂clockLaw x0, ∀ i, 0 ≤ e i := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ y ∂expMeasure 1, 0 ≤ y := by
    rw [ae_iff]
    have := cf_expMeasure_Iio 1
    simpa [not_le, Iio] using this
  have : IsProbabilityMeasure (expMeasure (1:ℝ)) := isProbabilityMeasure_expMeasure one_pos
  exact Measure.tendsto_eval_ae_ae.eventually h

lemma cf_saleTime_measurable (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ) (x0 k : ℕ) :
    Measurable (saleTime lam f π x0 k) := by
  unfold saleTime
  exact Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).div_const _)

lemma cf_saleTime_nonneg (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ) (x0 k : ℕ)
    (hlam : 0 < lam) (hf : Assumption1 f) (e : Fin x0 → ℝ) (he : ∀ i, 0 ≤ e i) :
    0 ≤ saleTime lam f π x0 k e := by
  unfold saleTime
  refine Finset.sum_nonneg (fun i _ => div_nonneg (he i) (mul_nonneg hlam.le ?_))
  exact setIntegral_nonneg measurableSet_Ioi (fun v _ => hf.nonnegative v)

lemma cf_clockLaw_prob (x0 : ℕ) : IsProbabilityMeasure (clockLaw x0) := by
  have : IsProbabilityMeasure (expMeasure (1:ℝ)) := isProbabilityMeasure_expMeasure one_pos
  unfold clockLaw
  infer_instance
lemma cf_Fbar_split (f : ℝ → ℝ) (hf : Assumption1 f) {a p : ℝ} (hap : a ≤ p) :
    Fbar f p = Fbar f a - ∫ v in a..p, f v := by
  have hint := hf.integrable
  unfold Fbar
  rw [← Ioc_union_Ioi_eq_Ioi hap,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn
      hint.integrableOn, intervalIntegral.integral_of_le hap]
  ring

lemma cf_Fbar_antitone (f : ℝ → ℝ) (hf : Assumption1 f) : Antitone (Fbar f) := by
  intro a b hab
  rw [cf_Fbar_split f hf hab]
  have : 0 ≤ ∫ v in a..b, f v :=
    intervalIntegral.integral_nonneg hab (fun u _ => hf.nonnegative u)
  linarith

lemma cf_Fbar_nonneg (f : ℝ → ℝ) (hf : Assumption1 f) (p : ℝ) : 0 ≤ Fbar f p :=
  setIntegral_nonneg measurableSet_Ioi (fun v _ => hf.nonnegative v)

/-- `(p - Δ) F̄(p)` is absolutely continuous with a.e. derivative `F̄ - (p - Δ) f`. -/
lemma cf_gain_identity (f : ℝ → ℝ) (hf : Assumption1 f) (Δ : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (b - Δ) * Fbar f b - (a - Δ) * Fbar f a =
      ∫ v in a..b, (Fbar f v - (v - Δ) * f v) := by
  set H : ℝ → ℝ := fun p => (p - Δ) * (Fbar f a - ∫ v in a..p, f v) with hH
  have hII : IntervalIntegrable f volume a b := hf.integrable.intervalIntegrable
  have hAC1 : AbsolutelyContinuousOnInterval (fun p : ℝ => p - Δ) a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    exact (contDiff_id.sub contDiff_const).contDiffOn
  have hAC2 : AbsolutelyContinuousOnInterval
      (fun p : ℝ => Fbar f a - ∫ v in a..p, f v) a b := by
    have h1 := hII.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
    have h0 : AbsolutelyContinuousOnInterval (fun _ : ℝ => Fbar f a) a b := by
      apply LipschitzOnWith.absolutelyContinuousOnInterval (K := 0)
      exact (LipschitzWith.const (Fbar f a)).lipschitzOnWith
    exact h0.sub h1
  have hAC : AbsolutelyContinuousOnInterval H a b := hAC1.fun_mul hAC2
  have hFTC := hAC.integral_deriv_eq_sub
  have hHb : H b = (b - Δ) * Fbar f b := by simp only [hH, ← cf_Fbar_split f hf hab]
  have hHa : H a = (a - Δ) * Fbar f a := by simp [hH]
  rw [← hHb, ← hHa, ← hFTC]
  apply intervalIntegral.integral_congr_ae
  have hLI : LocallyIntegrable f volume := hf.integrable.locallyIntegrable
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hLI] with x hx hxab
  have hx' : a ≤ x := by
    rw [uIoc_of_le hab] at hxab; exact hxab.1.le
  have hd : HasDerivAt H (1 * (Fbar f a - ∫ v in a..x, f v) + (x - Δ) * (0 - f x)) x := by
    have h1 : HasDerivAt (fun p : ℝ => p - Δ) 1 x := (hasDerivAt_id x).sub_const Δ
    have h2 : HasDerivAt (fun p : ℝ => Fbar f a - ∫ v in a..p, f v) (0 - f x) x :=
      (hasDerivAt_const x (Fbar f a)).sub (hx a)
    exact h1.mul h2
  rw [hd.deriv, ← cf_Fbar_split f hf hx']
  ring

/-- The root of `ψ(p) = Δ` maximizes `(p - Δ) F̄(p)` over `p ≥ 0`. -/
lemma cf_root_optimal (f : ℝ → ℝ) (hf : Assumption1 f) {Δ q p : ℝ} (hq : 0 ≤ q)
    (hψ : psi f q = Δ) (hp : 0 ≤ p) :
    (p - Δ) * Fbar f p ≤ (q - Δ) * Fbar f q := by
  have hkey : ∀ v, 0 ≤ v → Fbar f v - (v - Δ) * f v = f v * (Δ - psi f v) := by
    intro v hv
    have hfv : 0 < f v := hf.positive_of_nonnegative v hv
    unfold psi
    field_simp
    ring
  rcases le_total p q with hpq | hpq
  · have := cf_gain_identity f hf Δ hpq
    have hnn : 0 ≤ ∫ v in p..q, (Fbar f v - (v - Δ) * f v) := by
      apply intervalIntegral.integral_nonneg hpq
      intro u hu
      have hu0 : 0 ≤ u := hp.trans hu.1
      rw [hkey u hu0]
      have : psi f u ≤ psi f q :=
        hf.virtual_monotone (show u ∈ Ici (0:ℝ) from hu0) (show q ∈ Ici (0:ℝ) from hq) hu.2
      exact mul_nonneg (hf.nonnegative u) (by linarith)
    linarith
  · have := cf_gain_identity f hf Δ hpq
    have hnp : ∫ v in q..p, (Fbar f v - (v - Δ) * f v) ≤ 0 := by
      rw [← neg_nonneg, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_nonneg hpq
      intro u hu
      rw [neg_nonneg]
      have hu0 : 0 ≤ u := hq.trans hu.1
      rw [hkey u hu0]
      have : psi f q ≤ psi f u :=
        hf.virtual_monotone (show q ∈ Ici (0:ℝ) from hq) (show u ∈ Ici (0:ℝ) from hu0) hu.1
      exact mul_nonpos_of_nonneg_of_nonpos (hf.nonnegative u) (by linarith)
    linarith

/-- The Bellman value is attained at the root price. -/
lemma cf_bellman_eq (lam β : ℝ) (f : ℝ → ℝ) (V π : ℕ → ℝ) (hlam : 0 < lam)
    (hf : Assumption1 f) (hV : IsValueFn lam β f V) (hπ : IsRootPolicy f V π)
    (x : ℕ) (hx : 1 ≤ x) :
    β * V x = lam * Fbar f (π x) * (π x + V (x - 1) - V x) := by
  obtain ⟨hπ0, hψ, -⟩ := hπ x hx
  have hlub := hV.2 x hx
  apply le_antisymm
  · apply hlub.2
    rintro y ⟨p, hp, rfl⟩
    have := cf_root_optimal f hf hπ0 hψ hp
    have h2 : (p + V (x - 1) - V x) * Fbar f p ≤ (π x + V (x - 1) - V x) * Fbar f (π x) := by
      have e1 : p + V (x - 1) - V x = p - (V x - V (x - 1)) := by ring
      have e2 : π x + V (x - 1) - V x = π x - (V x - V (x - 1)) := by ring
      rw [e1, e2]; exact this
    nlinarith [mul_le_mul_of_nonneg_left h2 hlam.le]
  · exact hlub.1 ⟨π x, hπ0, rfl⟩

lemma cf_Fbar_pos (f : ℝ → ℝ) (hf : Assumption1 f) {p : ℝ} (hp : 0 ≤ p) : 0 < Fbar f p := by
  unfold Fbar
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun v => hf.nonnegative v))
    hf.integrable.integrableOn]
  have : Function.support f ∩ Ioi p = Ioi p := by
    ext v
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
    constructor
    · exact fun h => h.2
    · intro hv
      exact ⟨(hf.positive_of_nonnegative v (by linarith)).ne', hv⟩
  rw [this, Real.volume_Ioi]
  simp

lemma cf_exp_clock (c : ℝ) (hc : 0 ≤ c) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (-(c * y))) ∂expMeasure 1 = ENNReal.ofReal (1 / (1 + c)) := by
  rw [cf_lintegral_expMeasure 1 (by fun_prop), ← setLIntegral_congr Ioi_ae_eq_Ici]
  have h1 : ∀ y, ENNReal.ofReal (1 * Real.exp (-(1 * y))) * ENNReal.ofReal (Real.exp (-(c * y)))
      = ENNReal.ofReal (Real.exp (-((1 + c) * y))) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity), one_mul, ← Real.exp_add]
    congr 2; ring
  simp_rw [h1]
  have hc1 : 0 < 1 + c := by linarith
  have hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt (fun s => -Real.exp (-((1 + c) * s)) / (1 + c))
      (Real.exp (-((1 + c) * x))) x := by
    intro x _
    have := ((((hasDerivAt_id x).const_mul (1 + c)).neg.exp).neg).div_const (1 + c)
    refine this.congr_deriv ?_
    simp only [Pi.neg_apply, id, mul_one]
    field_simp
  have hpos : ∀ x ∈ Ioi (0:ℝ), 0 ≤ Real.exp (-((1 + c) * x)) := fun x _ => by positivity
  have htend : Tendsto (fun s => -Real.exp (-((1 + c) * s)) / (1 + c)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc1)
    have := (this.neg).div_const (1 + c)
    simpa [Function.comp_def] using this
  rw [cf_lintegral_Ioi_FTC hderiv hpos htend]
  congr 1
  simp only [mul_zero, neg_zero, Real.exp_zero, sub_neg_eq_add, zero_add]
  ring

lemma cf_disc_clock (lam β : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ) (x0 k : ℕ) (hβ : 0 < β)
    (hk : k ≤ x0) (hμ : ∀ i, i < k → 0 < lam * Fbar f (π (x0 - i))) :
    ∫⁻ e, ENNReal.ofReal (Real.exp (-(β * saleTime lam f π x0 k e))) ∂clockLaw x0 =
      ENNReal.ofReal (∏ i ∈ Finset.range k,
        lam * Fbar f (π (x0 - i)) / (lam * Fbar f (π (x0 - i)) + β)) := by
  set μ : ℕ → ℝ := fun i => lam * Fbar f (π (x0 - i)) with hμdef
  set g : Fin x0 → ℝ → ℝ := fun i y =>
    if i.val < k then Real.exp (-((β / μ i.val) * y)) else 1 with hgdef
  have hgnn : ∀ i y, 0 ≤ g i y := by
    intro i y; simp only [hgdef]; split_ifs <;> positivity
  have hprod : ∀ e : Fin x0 → ℝ, ENNReal.ofReal (Real.exp (-(β * saleTime lam f π x0 k e))) =
      ∏ i, ENNReal.ofReal (g i (e i)) := by
    intro e
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hgnn i (e i))]
    congr 1
    unfold saleTime
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum, Finset.prod_filter]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [hgdef, hμdef]
    split_ifs
    · congr 1; ring
    · rfl
  simp_rw [hprod]
  have hgm : ∀ i, Measurable (fun y => ENNReal.ofReal (g i y)) := by
    intro i; simp only [hgdef]; split_ifs <;> fun_prop
  have hexp1 : IsProbabilityMeasure (expMeasure (1:ℝ)) := isProbabilityMeasure_expMeasure one_pos
  have hind : iIndepFun (fun i (e : Fin x0 → ℝ) => ENNReal.ofReal (g i (e i))) (clockLaw x0) := by
    unfold clockLaw
    exact iIndepFun_pi (X := fun i y => ENNReal.ofReal (g i y)) (fun i => (hgm i).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hgm i).comp (measurable_pi_apply i))]
  have heval : ∀ i, ∫⁻ e, ENNReal.ofReal (g i (e i)) ∂clockLaw x0 =
      ∫⁻ y, ENNReal.ofReal (g i y) ∂expMeasure 1 := by
    intro i
    unfold clockLaw
    exact (measurePreserving_eval (fun _ : Fin x0 => expMeasure (1:ℝ)) i).lintegral_comp (hgm i)
  have hone : ∀ i : Fin x0, ∫⁻ y, ENNReal.ofReal (g i y) ∂expMeasure 1 =
      if i.val < k then ENNReal.ofReal (μ i.val / (μ i.val + β)) else 1 := by
    intro i
    simp only [hgdef]
    split_ifs with h
    · have hm := hμ i.val h
      rw [cf_exp_clock _ (div_nonneg hβ.le hm.le)]
      congr 1
      simp only [hμdef]
      generalize lam * Fbar f (π (x0 - ↑i)) = m at hm ⊢
      field_simp
    · simp [lintegral_const, measure_univ]
  simp_rw [heval, hone]
  rw [Fin.prod_univ_eq_prod_range
    (fun i => if i < k then ENNReal.ofReal (μ i / (μ i + β)) else 1) x0,
    ← Finset.prod_filter]
  have hfil : (Finset.range x0).filter (· < k) = Finset.range k := by
    ext i; simp; omega
  rw [hfil, ENNReal.ofReal_prod_of_nonneg]
  intro i hi
  have hm := hμ i (Finset.mem_range.1 hi)
  positivity

lemma cf_value_formula (V π q : ℕ → ℝ) (hrec : ∀ n, V (n + 1) = q (n + 1) * (π (n + 1) + V n))
    (h0 : V 0 = 0) :
    ∀ n, V n = ∑ m ∈ Finset.range n, π (n - m) * ∏ i ∈ Finset.range (m + 1), q (n - i) := by
  intro n
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [hrec, ih, Finset.sum_range_succ', mul_add, add_comm]
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.prod_range_succ' _ (m + 1)]
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      ring
    · rw [Finset.prod_range_one, Nat.sub_zero]
      ring

theorem solution (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ)
    (π : ℕ → ℝ) (x0 : ℕ) (hlam : 0 < lam) (hβ : 0 < β)
    (hf : Assumption1 f) (hV : IsValueFn lam β f V)
    (hπ : IsRootPolicy f V π) :
    ENNReal.ofReal (V x0) =
      ∫⁻ e, ENNReal.ofReal (discRevenue lam f π x0 β e) ∂clockLaw x0 := by
  set q : ℕ → ℝ := fun x => lam * Fbar f (π x) / (lam * Fbar f (π x) + β) with hqdef
  have hμpos : ∀ x, 1 ≤ x → 0 < lam * Fbar f (π x) :=
    fun x hx => mul_pos hlam (cf_Fbar_pos f hf (hπ x hx).1)
  have hrec : ∀ n, V (n + 1) = q (n + 1) * (π (n + 1) + V n) := by
    intro n
    have hb := cf_bellman_eq lam β f V π hlam hf hV hπ (n + 1) (by omega)
    have hm := hμpos (n + 1) (by omega)
    simp only [hqdef, Nat.add_sub_cancel] at hb ⊢
    field_simp
    linarith
  have hformula := cf_value_formula V π q hrec hV.1 x0
  have hπ0 : ∀ k ∈ Finset.Icc 1 x0, 0 ≤ π (x0 - k + 1) := by
    intro k hk
    have := Finset.mem_Icc.1 hk
    exact (hπ _ (by omega)).1
  have hS := cf_saleTime_measurable lam f π x0
  have hterm : ∀ k ∈ Finset.Icc 1 x0,
      ∫⁻ e, ENNReal.ofReal (π (x0 - k + 1) * Real.exp (-(β * saleTime lam f π x0 k e)))
        ∂clockLaw x0 =
      ENNReal.ofReal (π (x0 - k + 1) * ∏ i ∈ Finset.range k, q (x0 - i)) := by
    intro k hk
    have hk' := Finset.mem_Icc.1 hk
    simp_rw [ENNReal.ofReal_mul (hπ0 k hk)]
    rw [lintegral_const_mul _ (by
        have := hS k
        fun_prop),
      cf_disc_clock lam β f π x0 k hβ hk'.2 (fun i hi => hμpos _ (by omega))]
  unfold discRevenue
  rw [lintegral_congr (fun e => ENNReal.ofReal_sum_of_nonneg
      (fun k hk => mul_nonneg (hπ0 k hk) (Real.exp_pos _).le))]
  rw [lintegral_finsetSum _ (fun k _ => by
      have := hS k
      fun_prop),
    Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [hformula, Finset.range_eq_Ico]
    have hsh := Finset.sum_Ico_add'
      (fun k => π (x0 - k + 1) * ∏ i ∈ Finset.range k, q (x0 - i)) 0 x0 1
    have hI : Finset.Ico (0 + 1) (x0 + 1) = Finset.Icc 1 x0 := by
      ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hI] at hsh
    rw [← hsh]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have := Finset.mem_Ico.1 hm
    congr 2
    omega
  · intro k hk
    have hk' := Finset.mem_Icc.1 hk
    refine mul_nonneg (hπ0 k hk) (Finset.prod_nonneg (fun i hi => ?_))
    have := hμpos (x0 - i) (by have := Finset.mem_range.1 hi; omega)
    simp only [hqdef]
    positivity
