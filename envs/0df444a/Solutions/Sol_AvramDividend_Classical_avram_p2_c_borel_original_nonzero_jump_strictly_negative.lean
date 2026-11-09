-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_nonzero_jump_strictly_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:35:51.283203+00:00
-- url     : https://prove2.me/submissions/7b764259-c0dc-4444-bc48-2abcc916d09c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every genuine positive-time jump of the source spectrally negative
Lévy process is strictly negative, by its pathwise no-positive-jumps field. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0) (hu : 0 < u)
    (hjump : X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) :
    X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0 := by
  haveI : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hu⟩
  obtain ⟨l, hl⟩ := X.leftLim ω u hu
  have heq :
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = l :=
    leftLim_eq_of_tendsto hl
  rw [heq] at hjump ⊢
  have hle : X.X u ω ≤ l := X.noPosJumps ω u l hu hl
  have hne : X.X u ω ≠ l := by
    intro h
    apply hjump
    simp [h]
  exact sub_neg.mpr (lt_of_le_of_ne hle hne)
