-- Prove2me | solution 1 for AvramDividend.Classical.bv_jump_magnitude_sfinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T23:09:54.74985+00:00
-- url     : https://prove2.me/submissions/49937af7-89b0-4591-bfc0-604adcf2cfad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) :
    SFinite (X.ν.map (fun y : ℝ => Real.toNNReal (-y))) := by
  have hac : X.ν ≪ (volume : Measure ℝ) := by
    have h33 : X.Condition33 := hX.2.2
    unfold SpectrallyNegativeLevy.Condition33 at h33
    rcases h33 with hσ | hvar | hνac
    · exfalso
      rw [hbv.1] at hσ
      exact (lt_irrefl (0 : ℝ)) hσ
    · exfalso
      exact (ne_of_lt hbv.2) hvar
    · exact hνac
  letI : SFinite X.ν := sFinite_of_absolutelyContinuous hac
  let f : ℝ → ℝ≥0 := fun y => Real.toNNReal (-y)
  have hf : Measurable f := by fun_prop
  have hmap_meas :
      AEMeasurable f (Measure.sum (fun n : ℕ => sfiniteSeq X.ν n)) :=
    hf.aemeasurable
  have hmap :
      X.ν.map f =
        Measure.sum (fun n : ℕ => (sfiniteSeq X.ν n).map f) := by
    calc
      X.ν.map f =
          (Measure.sum (fun n : ℕ => sfiniteSeq X.ν n)).map f := by
            rw [sum_sfiniteSeq X.ν]
      _ = Measure.sum (fun n : ℕ => (sfiniteSeq X.ν n).map f) :=
        Measure.map_sum hmap_meas
  change SFinite (X.ν.map f)
  rw [hmap]
  infer_instance
