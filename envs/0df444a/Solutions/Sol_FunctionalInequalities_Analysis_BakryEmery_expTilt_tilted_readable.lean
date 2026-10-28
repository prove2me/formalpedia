-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.expTilt_tilted_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:17.533894+00:00
-- url     : https://prove2.me/submissions/f2dcc79b-cf1c-4f7c-9216-b33212dbabbe

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [m.IsAddHaarMeasure] in
/-- The exponential tilt of `m.tilted (-V)` is the tilted law of the potential `V - ⟪z, ·⟫`. -/
theorem solution {V : E → ℝ} (hV : Integrable (fun x => Real.exp ((-V) x)) m) (z : E) :
    FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z = m.tilted (-fun y => V y - ⟪z, y⟫) := by
    unfold FunctionalInequalities.Analysis.BakryEmery.expTilt
    first
    | rw [Measure.tilted_tilted hV]
    | rw [Measure.tilted_tilted' hV]
    | rw [Measure.tilted_tilted_of_integrable hV]
    | rw [Measure.tilted_tilted_eq_tilted_add hV]
    | rw [Measure.tilted_add hV]
    | rw [MeasureTheory.tilted_tilted hV]
    congr 1
    funext x
    change -V x + ⟪z, x⟫ = -(V x - ⟪z, x⟫)
    ring
