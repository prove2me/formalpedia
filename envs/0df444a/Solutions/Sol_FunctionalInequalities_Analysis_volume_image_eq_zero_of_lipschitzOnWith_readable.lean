-- Prove2me | solution 1 for FunctionalInequalities.Analysis.volume_image_eq_zero_of_lipschitzOnWith_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:31.099155+00:00
-- url     : https://prove2.me/submissions/733a9fa4-24da-47d8-8c57-1ab9afd35979

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Sard_Equidimensional

noncomputable section
open MeasureTheory Module Set
open scoped ENNReal NNReal RealInnerProductSpace
section LT12D1LipschitzNullImage
open MeasureTheory Set
/-- **Lipschitz maps send null sets to null sets** (weak Letwin route, Alexandrov's second-order
differentiability theorem): for a map of a finite-dimensional real inner product space into
itself that is Lipschitz on `s`, a Lebesgue-null `s` has a Lebesgue-null image. No measurability of `s`
is assumed. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {K : NNReal} {s : Set E} (hf : LipschitzOnWith K f s)
    (hs : (volume : Measure E) s = 0) : (volume : Measure E) (f '' s) = 0 := by
  have hsH : (μH[(Module.finrank ℝ E : ℝ)] : Measure E) s = 0 := by
    rw [Measure.isAddLeftInvariant_eq_smul
      (μH[(Module.finrank ℝ E : ℝ)] : Measure E) (volume : Measure E),
      Measure.smul_apply, hs, smul_zero]
  have himageH : (μH[(Module.finrank ℝ E : ℝ)] : Measure E) (f '' s) = 0 := by
    have h := hf.hausdorffMeasure_image_le (Nat.cast_nonneg (Module.finrank ℝ E))
    rw [hsH, mul_zero] at h
    exact le_antisymm h bot_le
  rw [Measure.isAddLeftInvariant_eq_smul
    (volume : Measure E) (μH[(Module.finrank ℝ E : ℝ)] : Measure E),
    Measure.smul_apply, himageH, smul_zero]
