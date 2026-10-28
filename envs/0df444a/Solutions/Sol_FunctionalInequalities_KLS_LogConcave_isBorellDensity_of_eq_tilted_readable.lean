-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.isBorellDensity_of_eq_tilted_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:40:19.247843+00:00
-- url     : https://prove2.me/submissions/5356d521-aa29-47dc-8cef-54091868be16

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_exp_neg_pos_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_rpow_mul_rpow_le_of_convexOn_readable

noncomputable section
open MeasureTheory Set
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
omit [FiniteDimensional ℝ V] in
/-- For continuous convex `W`, the density `e^{-W} / ∫ e^{-W} dm` of `ν = m.tilted (-W)` is a
log-concave Borell density with respect to `m`. -/
theorem solution {m : Measure V} {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) :
    FunctionalInequalities.KLS.IsBorellDensity (ν : Measure V) m (fun x => Real.exp (-W x) / ∫ y, Real.exp (-W y) ∂m) := by
  have hZ : 0 < ∫ y, Real.exp (-W y) ∂m :=
    FunctionalInequalities.KLS.LogConcave.integral_exp_neg_pos_of_eq_tilted_readable hνW
  have hcont :
      Continuous (fun x => Real.exp (-W x) / ∫ y, Real.exp (-W y) ∂m) :=
    (Real.continuous_exp.comp hW.neg).div_const _
  refine
    { measurable := hcont.measurable
      nonneg := fun x => div_nonneg (Real.exp_pos _).le hZ.le
      upperSemicontinuous := hcont.upperSemicontinuous
      logConcave := fun x y t ht0 ht1 =>
        FunctionalInequalities.KLS.LogConcave.rpow_mul_rpow_le_of_convexOn_readable hconv hZ x y ht0 ht1
      withDensity_eq := ?_ }
  rw [hνW]
  rfl
