-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_regularClass_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:36:39.625178+00:00
-- url     : https://prove2.me/submissions/3d4ccc0f-8b5a-482d-9ad3-b4c491cad962

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_rpow_mul_rpow_le_of_convexOn_readable

noncomputable section
open MeasureTheory Set
noncomputable section
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
set_option maxHeartbeats 500000 in
theorem FunctionalInequalities.KLS.LogConcave.isBorellDensity_of_eq_restricted_exp
    (μ : ProbabilityMeasure E) {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    {W : E → ℝ} (hW : Continuous W) (hWc : ConvexOn ℝ univ W)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))) :
    IsBorellDensity (μ : Measure E) volume (K.indicator fun x => Real.exp (-W x)) := by
  let f : E → ℝ := fun x => Real.exp (-W x)
  have hf : Continuous f := Real.continuous_exp.comp hW.neg
  have hnonneg : ∀ x, 0 ≤ K.indicator f x := fun x =>
    Set.indicator_nonneg (fun y _ => (Real.exp_pos (-W y)).le) x
  refine
    { measurable := hf.measurable.indicator hK.measurableSet
      nonneg := hnonneg
      upperSemicontinuous := ?_
      logConcave := ?_
      withDensity_eq := ?_ }
  · intro x a hxa
    by_cases hx : x ∈ K
    · have hfa : f x < a := by simpa only [Set.indicator_of_mem hx] using hxa
      have ha : 0 < a := (Real.exp_pos (-W x)).trans hfa
      filter_upwards [hf.upperSemicontinuous x a hfa] with y hy
      by_cases hyK : y ∈ K
      · simpa only [Set.indicator_of_mem hyK] using hy
      · simpa only [Set.indicator_of_notMem hyK] using ha
    · have ha : 0 < a := by simpa only [Set.indicator_of_notMem hx] using hxa
      filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
      simpa only [Set.indicator_of_notMem hy] using ha
  · intro x y t ht ht1
    by_cases hx : x ∈ K
    · by_cases hy : y ∈ K
      · have hz : t • x + (1-t) • y ∈ K :=
          hKc hx hy ht.le (by linarith) (by ring)
        simp only [Set.indicator_of_mem hx,Set.indicator_of_mem hy,Set.indicator_of_mem hz]
        simpa only [div_one] using rpow_mul_rpow_le_of_convexOn_readable hWc
          (by norm_num : (0 : ℝ) < 1) x y ht ht1
      · rw [Set.indicator_of_notMem hy,Real.zero_rpow (by linarith : 1-t ≠ 0),mul_zero]
        exact hnonneg _
    · rw [Set.indicator_of_notMem hx,Real.zero_rpow ht.ne',zero_mul]
      exact hnonneg _
  · rw [hμ]
    congr 1
    funext x
    by_cases hx : x ∈ K <;> simp [hx]
theorem FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_restricted_exp
    (μ : ProbabilityMeasure E) {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    {W : E → ℝ} (hW : Continuous W) (hWc : ConvexOn ℝ univ W)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))) :
    FunctionalInequalities.KLS.LogConcave μ :=
  IsBorellDensity.compactLogConcave (isBorellDensity_of_eq_restricted_exp μ hK hKc hW hWc hμ)
theorem solution
    (μ : ProbabilityMeasure E) {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    {W : E → ℝ} (hW : Continuous W) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))) :
    FunctionalInequalities.KLS.LogConcave μ := by
  have hWc : ConvexOn ℝ univ W := by
    have hn' : ConvexOn ℝ univ (fun y : E => ‖y‖ ^ 2) :=
      convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
    have hq := hn'.smul (show 0 ≤ κ / 2 by positivity)
    have he : (fun y => W y - κ / 2 * ‖y‖ ^ 2) +
        (fun y => (κ / 2) • ‖y‖ ^ 2) = W := by
      funext y
      simp only [Pi.add_apply,smul_eq_mul,sub_add_cancel]
    rw [← he]
    exact hstrong.add hq
  exact FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_restricted_exp μ hK hKc hW hWc hμ
