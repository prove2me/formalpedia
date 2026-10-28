-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.integral_eq_integral_mul_exp_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:04.749969+00:00
-- url     : https://prove2.me/submissions/c907d195-9924-4c0f-9e26-2a1cbe3149c5

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
omit [InnerProductSpace ℝ V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Change of measure from Haar measure to the tilted law: with `Z = ∫ e^{-U} dm`,
`∫ F dm = ∫ Z e^{U} F dν` for every `F`. -/
theorem solution (hνU : (ν : Measure V) = m.tilted (-U)) (F : V → ℝ) :
    ∫ x, F x ∂m = ∫ x, ((∫ y, Real.exp (-U y) ∂m) * Real.exp (U x)) * F x ∂(ν : Measure V) := by
  have hInt : Integrable (fun x => Real.exp (-U x)) m := by
    by_contra hnot
    have ht : m.tilted (-U) = 0 := by
      apply tilted_of_not_integrable
      exact hnot
    have hzero : (ν : Measure V) Set.univ = 0 := by
      rw [hνU, ht]
      simp
    have hone : (ν : Measure V) Set.univ = 1 := by
      simp
    rw [hzero] at hone
    norm_num at hone
  have hZ : 0 < ∫ y, Real.exp (-U y) ∂m := by
    exact integral_exp_pos hInt
  rw [hνU, integral_tilted]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  rw [div_eq_mul_inv]
  have hZ0 : (∫ y, Real.exp (-U y) ∂m) ≠ 0 := ne_of_gt hZ
  have hExp : Real.exp (-U x) * Real.exp (U x) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    F x =
        F x * (Real.exp (-U x) * Real.exp (U x)) := by
          rw [hExp]
          ring
    _ =
        (Real.exp (-U x) * (∫ y, Real.exp (-U y) ∂m)⁻¹) *
          ((∫ y, Real.exp (-U y) ∂m) * Real.exp (U x) * F x) := by
            field_simp [hZ0]
