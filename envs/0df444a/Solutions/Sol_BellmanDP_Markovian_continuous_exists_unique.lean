-- Prove2me | solution 1 for BellmanDP.Markovian.continuous_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:47:26.96823+00:00
-- url     : https://prove2.me/submissions/0e36bbb6-e509-4372-b1eb-c8a29047b37e

import Mathlib
import Definitions.Def_BellmanDP_Markovian_Continuous



namespace BellmanDP.Markovian

open MeasureTheory

lemma pc_ftc (f : ℝ → ℝ) (t : ℝ) (hf : IntervalIntegrable f volume 0 t) (n : ℕ) :
    ∫ s in (0:ℝ)..t, f s * (∫ r in (0:ℝ)..s, f r) ^ n =
      (∫ r in (0:ℝ)..t, f r) ^ (n + 1) / (n + 1) := by
  set G : ℝ → ℝ := fun s => ∫ r in (0:ℝ)..s, f r with hGdef
  have hG : AbsolutelyContinuousOnInterval G 0 t :=
    hf.absolutelyContinuousOnInterval_intervalIntegral (c := 0) Set.left_mem_uIcc
  have hGp : ∀ k : ℕ, AbsolutelyContinuousOnInterval (fun s => G s ^ k) 0 t := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero]
      refine LipschitzOnWith.absolutelyContinuousOnInterval (K := 0) ?_
      exact (LipschitzWith.const 1).lipschitzOnWith
    | succ k ih =>
      have := ih.fun_mul hG
      simpa [pow_succ] using this
  have h1 := (hGp (n + 1)).integral_deriv_eq_sub
  have hG0 : G 0 = 0 := by simp [G]
  rw [hG0, zero_pow (Nat.succ_ne_zero n), sub_zero] at h1
  have h2 : ∫ s in (0:ℝ)..t, deriv (fun s => G s ^ (n + 1)) s =
      ∫ s in (0:ℝ)..t, ((n:ℝ) + 1) * (f s * G s ^ n) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hf.ae_hasDerivAt_integral] with s hs hsI
    have hd := hs (Set.uIoc_subset_uIcc hsI) 0 Set.left_mem_uIcc
    have := (hd.pow (n + 1)).deriv
    rw [show (fun s => G s ^ (n + 1)) = (fun x => ∫ t in (0:ℝ)..x, f t) ^ (n + 1) from rfl, this]
    simp only [G, Nat.add_sub_cancel]
    push_cast
    ring
  rw [h2, intervalIntegral.integral_const_mul] at h1
  rw [eq_div_iff (by positivity), mul_comm, h1]


lemma pc_integrable {N : ℕ} (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) (f : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hf : IntegrableOn f (Set.Icc 0 T))
    (hlip : ∀ t ∈ Set.Icc 0 T, ∀ x y : Fin N → ℝ, ‖F t x - F t y‖ ≤ f t * ‖x - y‖)
    (hbd : ∀ t ∈ Set.Icc 0 T, ‖F t 0‖ ≤ f t)
    (hmeas : ∀ x : Fin N → ℝ, Measurable fun t => F t x)
    (x : ℝ → Fin N → ℝ) (hx : ContinuousOn x (Set.Icc 0 T)) :
    IntegrableOn (fun s => F s (x s)) (Set.Icc 0 T) := by
  let cl : ℝ → ℝ := fun s => max 0 (min s T)
  have hcl : ∀ s, cl s ∈ Set.Icc 0 T := fun s =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hcl' : ∀ s ∈ Set.Icc 0 T, cl s = s := by
    rintro s ⟨h0, h1⟩
    simp [cl, min_eq_left h1, max_eq_right h0]
  let u : (Fin N → ℝ) → ℝ → (Fin N → ℝ) := fun y s => F (cl s) y
  have hu_cont : ∀ s, Continuous fun y => u y s := by
    intro s
    have hL : LipschitzWith (Real.toNNReal (f (cl s))) (fun y => F (cl s) y) := by
      refine LipschitzWith.of_dist_le' fun y z => ?_
      rw [dist_eq_norm, dist_eq_norm]
      exact hlip _ (hcl s) y z
    exact hL.continuous
  have hu_meas : ∀ y, Measurable (u y) := fun y =>
    (hmeas y).comp (by fun_prop : Continuous cl).measurable
  have hjoint : Measurable (Function.uncurry u) :=
    measurable_uncurry_of_continuous_of_measurable hu_cont hu_meas
  have hxm : AEMeasurable x (volume.restrict (Set.Icc 0 T)) :=
    hx.aemeasurable measurableSet_Icc
  have hcomp : AEMeasurable (fun s => u (x s) s) (volume.restrict (Set.Icc 0 T)) :=
    hjoint.comp_aemeasurable (hxm.prodMk aemeasurable_id)
  have hcomp' : AEMeasurable (fun s => F s (x s)) (volume.restrict (Set.Icc 0 T)) := by
    refine hcomp.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simp only [u, hcl' s hs]
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  refine Integrable.mono' (hf.mul_const (K + 1)) hcomp'.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have h1 := hlip s hs (x s) 0
  have h2 := hbd s hs
  have h3 := hK s hs
  have hf0 : 0 ≤ f s := by
    have := hlip s hs 0 (fun _ => 1)
    by_contra hc
    push_neg at hc
    have h4 : 0 < ‖(0 : Fin N → ℝ) - fun _ => 1‖ ∨ ‖(0 : Fin N → ℝ) - fun _ => 1‖ = 0 :=
      (norm_nonneg _).lt_or_eq'
    have := norm_nonneg (F s 0 - F s fun _ => 1)
    nlinarith [norm_nonneg ((0 : Fin N → ℝ) - fun _ => 1), norm_nonneg (F s 0)]
  rw [sub_zero] at h1
  calc ‖F s (x s)‖ ≤ ‖F s (x s) - F s 0‖ + ‖F s 0‖ := norm_le_norm_sub_add _ _
    _ ≤ f s * ‖x s‖ + f s := add_le_add h1 h2
    _ ≤ f s * K + f s := by nlinarith
    _ = f s * (K + 1) := by ring

lemma pc_diff_le {N : ℕ} (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) (f : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hf : IntegrableOn f (Set.Icc 0 T)) (hf0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ f t)
    (hlip : ∀ t ∈ Set.Icc 0 T, ∀ x y : Fin N → ℝ, ‖F t x - F t y‖ ≤ f t * ‖x - y‖)
    (hbd : ∀ t ∈ Set.Icc 0 T, ‖F t 0‖ ≤ f t)
    (hmeas : ∀ x : Fin N → ℝ, Measurable fun t => F t x)
    (u v : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Set.Icc 0 T)) (hv : ContinuousOn v (Set.Icc 0 T))
    (B : ℝ → ℝ) (hBc : ContinuousOn B (Set.Icc 0 T))
    (hB : ∀ s ∈ Set.Icc 0 T, ‖u s - v s‖ ≤ B s) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖(∫ s in (0:ℝ)..t, F s (u s)) - ∫ s in (0:ℝ)..t, F s (v s)‖ ≤ ∫ s in (0:ℝ)..t, f s * B s := by
  have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  have II : ∀ g : ℝ → ℝ → Fin N → ℝ, IntegrableOn (fun s => g s s) (Set.Icc 0 T) → True :=
    fun _ _ => trivial
  have hIu : IntervalIntegrable (fun s => F s (u s)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
    exact (pc_integrable F f T hT hf hlip hbd hmeas u hu).mono_set hsub
  have hIv : IntervalIntegrable (fun s => F s (v s)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
    exact (pc_integrable F f T hT hf hlip hbd hmeas v hv).mono_set hsub
  have hIB : IntervalIntegrable (fun s => f s * B s) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
    exact (hf.mono_set hsub).mul_continuousOn (hBc.mono hsub) isCompact_Icc
  rw [← intervalIntegral.integral_sub hIu hIv]
  refine intervalIntegral.norm_integral_le_of_norm_le ht.1
    (Filter.Eventually.of_forall fun s hs => ?_) hIB
  have hs' : s ∈ Set.Icc 0 T := ⟨hs.1.le, hs.2.trans ht.2⟩
  exact (hlip s hs' _ _).trans (mul_le_mul_of_nonneg_left (hB s hs') (hf0 s hs'))

lemma pc_G_cont (f : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T) (hf : IntegrableOn f (Set.Icc 0 T)) :
    ContinuousOn (fun s => ∫ r in (0:ℝ)..s, f r) (Set.Icc 0 T) := by
  have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T) (μ := volume)
    (f := f) (by rw [Set.uIcc_of_le hT]; exact hf)
  rwa [Set.uIcc_of_le hT] at this

lemma pc_step {N : ℕ} (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) (f : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hf : IntegrableOn f (Set.Icc 0 T)) (hf0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ f t)
    (hlip : ∀ t ∈ Set.Icc 0 T, ∀ x y : Fin N → ℝ, ‖F t x - F t y‖ ≤ f t * ‖x - y‖)
    (hbd : ∀ t ∈ Set.Icc 0 T, ‖F t 0‖ ≤ f t)
    (hmeas : ∀ x : Fin N → ℝ, Measurable fun t => F t x)
    (u v : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Set.Icc 0 T)) (hv : ContinuousOn v (Set.Icc 0 T))
    (K : ℝ) (n : ℕ)
    (hB : ∀ s ∈ Set.Icc 0 T, ‖u s - v s‖ ≤ K * (∫ r in (0:ℝ)..s, f r) ^ n / n.factorial)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖(∫ s in (0:ℝ)..t, F s (u s)) - ∫ s in (0:ℝ)..t, F s (v s)‖ ≤
      K * (∫ r in (0:ℝ)..t, f r) ^ (n + 1) / (n + 1).factorial := by
  have hBc : ContinuousOn (fun s => K * (∫ r in (0:ℝ)..s, f r) ^ n / n.factorial)
      (Set.Icc 0 T) :=
    ((continuousOn_const.mul ((pc_G_cont f T hT hf).pow n)).div_const _)
  refine (pc_diff_le F f T hT hf hf0 hlip hbd hmeas u v hu hv _ hBc hB t ht).trans (le_of_eq ?_)
  have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  have hfi : IntervalIntegrable f volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]; exact hf.mono_set hsub
  have e : (fun s => f s * (K * (∫ r in (0:ℝ)..s, f r) ^ n / n.factorial)) =
      fun s => (K / n.factorial) * (f s * (∫ r in (0:ℝ)..s, f r) ^ n) := by
    funext s; ring
  rw [e, intervalIntegral.integral_const_mul, pc_ftc f t hfi n, Nat.factorial_succ]
  push_cast
  field_simp

/-- the limit of the successive approximations. -/
noncomputable def pcLim {N : ℕ} (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) (c : Fin N → ℝ) (t : ℝ) :
    Fin N → ℝ :=
  c + ∑' k, (picardIter F c (k + 1) t - picardIter F c k t)

lemma pc_core {N : ℕ} (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) (f : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hf : IntegrableOn f (Set.Icc 0 T)) (hf0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ f t)
    (hlip : ∀ t ∈ Set.Icc 0 T, ∀ x y : Fin N → ℝ, ‖F t x - F t y‖ ≤ f t * ‖x - y‖)
    (hbd : ∀ t ∈ Set.Icc 0 T, ‖F t 0‖ ≤ f t)
    (hmeas : ∀ x : Fin N → ℝ, Measurable fun t => F t x) (c : Fin N → ℝ) :
    IsIntegralSolutionOn F c T (pcLim F c) ∧
      (∀ z : ℝ → Fin N → ℝ, IsIntegralSolutionOn F c T z → Set.EqOn z (pcLim F c) (Set.Icc 0 T)) ∧
      TendstoUniformlyOn (picardIter F c) (pcLim F c) Filter.atTop (Set.Icc 0 T) := by
  set P := picardIter F c with hPdef
  set G : ℝ → ℝ := fun s => ∫ r in (0:ℝ)..s, f r with hGdef
  have hP0 : ∀ t, P 0 t = c := fun t => rfl
  have hPs : ∀ n t, P (n + 1) t = c + ∫ s in (0:ℝ)..t, F s (P n s) := fun n t => rfl
  have hInt := pc_integrable F f T hT hf hlip hbd hmeas
  have hPc : ∀ n, ContinuousOn (P n) (Set.Icc 0 T) := by
    intro n
    induction n with
    | zero => exact continuousOn_const
    | succ n ih =>
      have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T) (μ := volume)
        (f := fun s => F s (P n s)) (by rw [Set.uIcc_of_le hT]; exact hInt _ ih)
      rw [Set.uIcc_of_le hT] at this
      exact continuousOn_const.add this
  have hGnn : ∀ t ∈ Set.Icc 0 T, 0 ≤ G t := fun t ht =>
    intervalIntegral.integral_nonneg ht.1 fun s hs => hf0 s ⟨hs.1, hs.2.trans ht.2⟩
  have hfi : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → IntervalIntegrable f volume a b := by
    intro a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hf.mono_set (Set.Icc_subset_Icc ha hb)
  have hGmono : ∀ t ∈ Set.Icc 0 T, G t ≤ G T := by
    intro t ht
    have e := intervalIntegral.integral_interval_sub_left (hfi 0 T le_rfl hT le_rfl)
      (hfi 0 t le_rfl ht.1 ht.2)
    have : 0 ≤ ∫ x in t..T, f x :=
      intervalIntegral.integral_nonneg ht.2 fun s hs => hf0 s ⟨ht.1.trans hs.1, hs.2⟩
    simp only [G]; linarith
  have hGT : 0 ≤ G T := hGnn T ⟨hT, le_rfl⟩
  set M := (‖c‖ + 1) * G T with hM
  have hM0 : 0 ≤ M := mul_nonneg (by positivity) hGT
  -- base estimate
  have hbase : ∀ t ∈ Set.Icc 0 T, ‖P 1 t - P 0 t‖ ≤ M := by
    intro t ht
    rw [hPs, hP0, add_sub_cancel_left]
    have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
    have hb : IntervalIntegrable (fun s => f s * (‖c‖ + 1)) volume 0 t :=
      (hfi 0 t le_rfl ht.1 ht.2).mul_const _
    refine (intervalIntegral.norm_integral_le_of_norm_le ht.1
      (Filter.Eventually.of_forall fun s hs => ?_) hb).trans ?_
    · have hs' : s ∈ Set.Icc 0 T := ⟨hs.1.le, hs.2.trans ht.2⟩
      have h1 := hlip s hs' c 0
      rw [sub_zero] at h1
      calc ‖F s (P 0 s)‖ = ‖F s c‖ := rfl
        _ ≤ ‖F s c - F s 0‖ + ‖F s 0‖ := norm_le_norm_sub_add _ _
        _ ≤ f s * ‖c‖ + f s := add_le_add h1 (hbd s hs')
        _ = f s * (‖c‖ + 1) := by ring
    · rw [intervalIntegral.integral_mul_const, hM, mul_comm]
      exact mul_le_mul_of_nonneg_left (hGmono t ht) (by positivity)
  have hbound : ∀ n, ∀ t ∈ Set.Icc 0 T, ‖P (n + 1) t - P n t‖ ≤ M * G t ^ n / n.factorial := by
    intro n
    induction n with
    | zero =>
      intro t ht
      simpa using hbase t ht
    | succ n ih =>
      intro t ht
      rw [hPs (n + 1), hPs n, add_sub_add_left_eq_sub]
      exact pc_step F f T hT hf hf0 hlip hbd hmeas _ _ (hPc (n + 1)) (hPc n) M n ih t ht
  -- uniform convergence
  have hsum : Summable (fun k : ℕ => M * (G T ^ k / k.factorial)) :=
    (Real.summable_pow_div_factorial (G T)).mul_left M
  have hU := tendstoUniformlyOn_tsum_nat hsum (s := Set.Icc 0 T)
    (f := fun k t => P (k + 1) t - P k t) (by
      intro k t ht
      refine (hbound k t ht).trans ?_
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hM0
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (hGnn t ht) (hGmono t ht) k)
        (by positivity))
  have hPsum : ∀ n t, P n t = c + ∑ k ∈ Finset.range n, (P (k + 1) t - P k t) := by
    intro n t
    rw [Finset.sum_range_sub (fun k => P k t), hP0]; abel
  have hUP : TendstoUniformlyOn P (pcLim F c) Filter.atTop (Set.Icc 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
    intro ε hε
    filter_upwards [hU ε hε] with n hn t ht
    rw [hPsum n t]
    simp only [pcLim, dist_add_left]
    exact hn t ht
  have hxc : ContinuousOn (pcLim F c) (Set.Icc 0 T) :=
    hUP.continuousOn (Filter.Eventually.of_forall hPc).frequently
  have hlimP : ∀ t ∈ Set.Icc 0 T, Filter.Tendsto (fun n => P n t) Filter.atTop
      (nhds (pcLim F c t)) := fun t ht => hUP.tendsto_at ht
  -- solution property
  have hsol : ∀ t ∈ Set.Icc 0 T, pcLim F c t = c + ∫ s in (0:ℝ)..t, F s (pcLim F c s) := by
    intro t ht
    have h1 : Filter.Tendsto (fun n => P (n + 1) t) Filter.atTop (nhds (pcLim F c t)) :=
      (hlimP t ht).comp (Filter.tendsto_add_atTop_nat 1)
    have h2 : Filter.Tendsto (fun n => P (n + 1) t) Filter.atTop
        (nhds (c + ∫ s in (0:ℝ)..t, F s (pcLim F c s))) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hε' : 0 < ε / (G T + 1) := div_pos hε (by linarith)
      obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1
        ((Metric.tendstoUniformlyOn_iff.1 hUP) _ hε')
      refine ⟨N0, fun n hn => ?_⟩
      rw [hPs, dist_eq_norm, add_sub_add_left_eq_sub]
      have hB : ∀ s ∈ Set.Icc 0 T, ‖P n s - pcLim F c s‖ ≤ ε / (G T + 1) := by
        intro s hs
        have := hN0 n hn s hs
        rw [dist_eq_norm, norm_sub_rev] at this
        exact this.le
      refine lt_of_le_of_lt (pc_diff_le F f T hT hf hf0 hlip hbd hmeas _ _ (hPc n) hxc _
        continuousOn_const hB t ht) ?_
      rw [intervalIntegral.integral_mul_const]
      calc G t * (ε / (G T + 1)) ≤ G T * (ε / (G T + 1)) :=
            mul_le_mul_of_nonneg_right (hGmono t ht) hε'.le
        _ < (G T + 1) * (ε / (G T + 1)) := by
            apply mul_lt_mul_of_pos_right (by linarith) hε'
        _ = ε := by field_simp
    exact tendsto_nhds_unique h1 h2
  refine ⟨⟨hxc, hInt _ hxc, hsol⟩, fun z hz => ?_, hUP⟩
  -- uniqueness
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hz.1.sub continuousOn_const)
  have hzb : ∀ n, ∀ t ∈ Set.Icc 0 T, ‖z t - P n t‖ ≤ C * G t ^ n / n.factorial := by
    intro n
    induction n with
    | zero =>
      intro t ht
      simpa [hP0] using hC t ht
    | succ n ih =>
      intro t ht
      rw [hz.2.2 t ht, hPs n, add_sub_add_left_eq_sub]
      exact pc_step F f T hT hf hf0 hlip hbd hmeas _ _ hz.1 (hPc n) C n ih t ht
  intro t ht
  have hz1 : Filter.Tendsto (fun n => P n t) Filter.atTop (nhds (z t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Filter.Tendsto (fun n : ℕ => C * (G T ^ n / n.factorial)) Filter.atTop
        (nhds 0) := by
      simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (G T)).const_mul C
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
    rw [norm_sub_rev]
    refine (hzb n t ht).trans ?_
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC t ht)
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (hGnn t ht) (hGmono t ht) n)
      (by positivity)
  exact tendsto_nhds_unique hz1 (hlimP t ht)

lemma pc_rowdiff {N : ℕ} (a : Fin N → ℝ) (L : ℝ) (ha : ∑ j, |a j| ≤ L) (x y : Fin N → ℝ) :
    ∑ j, a j * x j - ∑ j, a j * y j ≤ L * ‖x - y‖ := by
  rw [← Finset.sum_sub_distrib]
  calc ∑ j, (a j * x j - a j * y j) ≤ ∑ j, |a j| * ‖x - y‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← mul_sub]
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have := norm_le_pi_norm (x - y) j
        rw [Real.norm_eq_abs] at this
        simpa using this
    _ = (∑ j, |a j|) * ‖x - y‖ := by rw [Finset.sum_mul]
    _ ≤ L * ‖x - y‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)

lemma pc_normle {N : ℕ} (v : Fin N → ℝ) (r : ℝ) (hr : 0 ≤ r) (h : ∀ i, |v i| ≤ r) : ‖v‖ ≤ r := by
  rw [pi_norm_le_iff_of_nonneg hr]
  intro i; rw [Real.norm_eq_abs]; exact h i

theorem minmax_core {N : ℕ} {P Q : Fin N → Type*}
    (A : (i : Fin N) → P i → Q i → ℝ → Fin N → ℝ) (b : (i : Fin N) → P i → Q i → ℝ → ℝ)
    (SP : (i : Fin N) → Set (P i)) (SQ : (i : Fin N) → Set (Q i))
    (V : ℝ → (Fin N → ℝ) → Fin N → ℝ) (hV : IsRowwiseSaddleValue A b SP SQ V)
    (hVmeas : ∀ x : Fin N → ℝ, Measurable fun t => V t x)
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Icc 0 T))
    (hA : ∀ t : ℝ, 0 ≤ t → ∀ p ∈ Set.pi Set.univ SP, ∀ q ∈ Set.pi Set.univ SQ,
      ∑ i, ∑ j, |A i (p i) (q i) t j| ≤ f t)
    (hb : ∀ t : ℝ, 0 ≤ t → ∀ p ∈ Set.pi Set.univ SP, ∀ q ∈ Set.pi Set.univ SQ,
      ∑ i, |b i (p i) (q i) t| ≤ f t)
    (c : Fin N → ℝ) :
    ∃ x : ℝ → Fin N → ℝ, IsIntegralSolutionOn V c T x ∧
      (∀ z : ℝ → Fin N → ℝ, IsIntegralSolutionOn V c T z → Set.EqOn z x (Set.Icc 0 T)) ∧
      TendstoUniformlyOn (picardIter V c) x Filter.atTop (Set.Icc 0 T) := by
  classical
  let p0 : (i : Fin N) → P i := fun i => (hV 0 0 i).choose
  have p0m : ∀ i, p0 i ∈ SP i := fun i => (hV 0 0 i).choose_spec.1
  let q0 : (i : Fin N) → Q i := fun i => (hV 0 0 i).choose_spec.2.choose
  have q0m : ∀ i, q0 i ∈ SQ i := fun i => (hV 0 0 i).choose_spec.2.choose_spec.1
  have rowA : ∀ t, 0 ≤ t → ∀ i, ∀ p ∈ SP i, ∀ q ∈ SQ i, ∑ j, |A i p q t j| ≤ f t := by
    intro t ht i p hp q hq
    have hpm : Function.update p0 i p ∈ Set.pi Set.univ SP := by
      intro k _
      by_cases hk : k = i
      · subst hk; simpa using hp
      · simpa [Function.update_of_ne hk] using p0m k
    have hqm : Function.update q0 i q ∈ Set.pi Set.univ SQ := by
      intro k _
      by_cases hk : k = i
      · subst hk; simpa using hq
      · simpa [Function.update_of_ne hk] using q0m k
    refine le_trans ?_ (hA t ht _ hpm _ hqm)
    have := Finset.single_le_sum (f := fun k => ∑ j, |A k (Function.update p0 i p k)
      (Function.update q0 i q k) t j|) (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
    simpa using this
  have rowb : ∀ t, 0 ≤ t → ∀ i, ∀ p ∈ SP i, ∀ q ∈ SQ i, |b i p q t| ≤ f t := by
    intro t ht i p hp q hq
    have hpm : Function.update p0 i p ∈ Set.pi Set.univ SP := by
      intro k _
      by_cases hk : k = i
      · subst hk; simpa using hp
      · simpa [Function.update_of_ne hk] using p0m k
    have hqm : Function.update q0 i q ∈ Set.pi Set.univ SQ := by
      intro k _
      by_cases hk : k = i
      · subst hk; simpa using hq
      · simpa [Function.update_of_ne hk] using q0m k
    refine le_trans ?_ (hb t ht _ hpm _ hqm)
    have := Finset.single_le_sum (f := fun k => |b k (Function.update p0 i p k)
      (Function.update q0 i q k) t|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
    simpa using this
  have hf0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ f t := fun t ht =>
    (Finset.sum_nonneg fun i _ => abs_nonneg _).trans (hb t ht.1 p0 (fun i _ => p0m i) q0
      (fun i _ => q0m i))
  have half : ∀ t, 0 ≤ t → ∀ x y : Fin N → ℝ, ∀ i, V t x i - V t y i ≤ f t * ‖x - y‖ := by
    intro t ht x y i
    obtain ⟨px, hpx, qx, hqx, hx1, hx2⟩ := hV t x i
    obtain ⟨py, hpy, qy, hqy, hy1, hy2⟩ := hV t y i
    have e1 := hx2 qy hqy
    have e2 := hy1 px hpx
    simp only [rowAffine2] at e1 e2
    have := pc_rowdiff (fun j => A i px qy t j) (f t) (rowA t ht i px hpx qy hqy) x y
    linarith
  have hlip : ∀ t ∈ Set.Icc 0 T, ∀ x y : Fin N → ℝ, ‖V t x - V t y‖ ≤ f t * ‖x - y‖ := by
    intro t ht x y
    refine pc_normle _ _ (mul_nonneg (hf0 t ht) (norm_nonneg _)) fun i => ?_
    rw [Pi.sub_apply, abs_sub_le_iff]
    refine ⟨half t ht.1 x y i, ?_⟩
    rw [norm_sub_rev]; exact half t ht.1 y x i
  have hbd : ∀ t ∈ Set.Icc 0 T, ‖V t 0‖ ≤ f t := by
    intro t ht
    refine pc_normle _ _ (hf0 t ht) fun i => ?_
    obtain ⟨p, hp, q, hq, h1, h2⟩ := hV t 0 i
    have e1 := h1 p hp
    have e2 := h2 q hq
    simp only [rowAffine2, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at e1 e2
    rw [le_antisymm e2 e1]
    exact rowb t ht.1 i p hp q hq
  exact ⟨pcLim V c, pc_core V f T hT.le hf hf0 hlip hbd hVmeas c⟩

theorem continuous_core {N : ℕ} {Q : Fin N → Type*}
    (A : (i : Fin N) → Q i → ℝ → Fin N → ℝ) (b : (i : Fin N) → Q i → ℝ → ℝ)
    (S : (i : Fin N) → Set (Q i)) (f : ℝ → ℝ)
    (hf : ∀ T : ℝ, IntegrableOn f (Set.Icc 0 T))
    (hA : ∀ t : ℝ, 0 ≤ t → ∀ q ∈ Set.pi Set.univ S, ∑ i, ∑ j, |A i (q i) t j| ≤ f t)
    (hb : ∀ t : ℝ, 0 ≤ t → ∀ q ∈ Set.pi Set.univ S, ∑ i, |b i (q i) t| ≤ f t)
    (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) (hF : IsRowwiseMax A b S F)
    (hFmeas : ∀ x : Fin N → ℝ, Measurable fun t => F t x) (c : Fin N → ℝ) :
    ∃ x : ℝ → Fin N → ℝ,
      (∀ T : ℝ, 0 < T → IsIntegralSolutionOn F c T x) ∧
      (∀ S' : ℝ, 0 < S' → ∀ z : ℝ → Fin N → ℝ, IsIntegralSolutionOn F c S' z →
        Set.EqOn z x (Set.Icc 0 S')) ∧
      (∀ T : ℝ, 0 < T → TendstoUniformlyOn (picardIter F c) x Filter.atTop (Set.Icc 0 T)) := by
  classical
  let q0 : (i : Fin N) → Q i := fun i => ((hF 0 0 i).1).choose
  have q0m : ∀ i, q0 i ∈ S i := fun i => ((hF 0 0 i).1).choose_spec.1
  have rowA : ∀ t, 0 ≤ t → ∀ i, ∀ q ∈ S i, ∑ j, |A i q t j| ≤ f t := by
    intro t ht i q hq
    have hqm : Function.update q0 i q ∈ Set.pi Set.univ S := by
      intro k _
      by_cases hk : k = i
      · subst hk; simpa using hq
      · simpa [Function.update_of_ne hk] using q0m k
    refine le_trans ?_ (hA t ht _ hqm)
    have := Finset.single_le_sum (f := fun k => ∑ j, |A k (Function.update q0 i q k) t j|)
      (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
    simpa using this
  have rowb : ∀ t, 0 ≤ t → ∀ i, ∀ q ∈ S i, |b i q t| ≤ f t := by
    intro t ht i q hq
    have hqm : Function.update q0 i q ∈ Set.pi Set.univ S := by
      intro k _
      by_cases hk : k = i
      · subst hk; simpa using hq
      · simpa [Function.update_of_ne hk] using q0m k
    refine le_trans ?_ (hb t ht _ hqm)
    have := Finset.single_le_sum (f := fun k => |b k (Function.update q0 i q k) t|)
      (fun k _ => abs_nonneg _) (Finset.mem_univ i)
    simpa using this
  have hf0 : ∀ t, 0 ≤ t → 0 ≤ f t := fun t ht =>
    (Finset.sum_nonneg fun i _ => abs_nonneg _).trans (hb t ht q0 (fun i _ => q0m i))
  have half : ∀ t, 0 ≤ t → ∀ x y : Fin N → ℝ, ∀ i, F t x i - F t y i ≤ f t * ‖x - y‖ := by
    intro t ht x y i
    obtain ⟨⟨qx, hqx, ex⟩, -⟩ := hF t x i
    have e2 := (hF t y i).2 ⟨qx, hqx, rfl⟩
    simp only [rowAffine] at ex e2
    have := pc_rowdiff (fun j => A i qx t j) (f t) (rowA t ht i qx hqx) x y
    linarith
  have hlip : ∀ T, ∀ t ∈ Set.Icc 0 T, ∀ x y : Fin N → ℝ, ‖F t x - F t y‖ ≤ f t * ‖x - y‖ := by
    intro T t ht x y
    refine pc_normle _ _ (mul_nonneg (hf0 t ht.1) (norm_nonneg _)) fun i => ?_
    rw [Pi.sub_apply, abs_sub_le_iff]
    refine ⟨half t ht.1 x y i, ?_⟩
    rw [norm_sub_rev]; exact half t ht.1 y x i
  have hbd : ∀ T, ∀ t ∈ Set.Icc 0 T, ‖F t 0‖ ≤ f t := by
    intro T t ht
    refine pc_normle _ _ (hf0 t ht.1) fun i => ?_
    obtain ⟨⟨q, hq, e⟩, -⟩ := hF t 0 i
    simp only [rowAffine, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at e
    rw [← e]
    exact rowb t ht.1 i q hq
  have core := fun T (hT : 0 < T) =>
    pc_core F f T hT.le (hf T) (fun t ht => hf0 t ht.1) (hlip T) (hbd T) hFmeas c
  exact ⟨pcLim F c, fun T hT => (core T hT).1, fun S' hS' z hz => (core S' hS').2.1 z hz,
    fun T hT => (core T hT).2.2⟩
end BellmanDP.Markovian

open BellmanDP.Markovian
open MeasureTheory

theorem solution {N : ℕ} {Q : Fin N → Type*}
    (A : (i : Fin N) → Q i → ℝ → Fin N → ℝ) (b : (i : Fin N) → Q i → ℝ → ℝ)
    (S : (i : Fin N) → Set (Q i)) (f : ℝ → ℝ)
    (hf : ∀ T : ℝ, IntegrableOn f (Set.Icc 0 T))
    (hA : ∀ t : ℝ, 0 ≤ t → ∀ q ∈ Set.pi Set.univ S, ∑ i, ∑ j, |A i (q i) t j| ≤ f t)
    (hb : ∀ t : ℝ, 0 ≤ t → ∀ q ∈ Set.pi Set.univ S, ∑ i, |b i (q i) t| ≤ f t)
    (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) (hF : IsRowwiseMax A b S F)
    (hFmeas : ∀ x : Fin N → ℝ, Measurable fun t => F t x) (c : Fin N → ℝ) :
    ∃ x : ℝ → Fin N → ℝ,
      (∀ T : ℝ, 0 < T → IsIntegralSolutionOn F c T x) ∧
      (∀ S' : ℝ, 0 < S' → ∀ z : ℝ → Fin N → ℝ, IsIntegralSolutionOn F c S' z →
        Set.EqOn z x (Set.Icc 0 S')) ∧
      (∀ T : ℝ, 0 < T → TendstoUniformlyOn (picardIter F c) x Filter.atTop (Set.Icc 0 T)) := by
  exact continuous_core A b S f hf hA hb F hF hFmeas c
