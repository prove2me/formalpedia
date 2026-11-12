-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18i_original_zero_cutoff_gaussian_square_integrable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:09:27.884061+00:00
-- url     : https://prove2.me/submissions/4fa3a06e-aeb1-4159-a8f6-b9575b82f3de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18j_finite_activity_countable_real_model_square
import Theorems.Thm_AvramDividend_Classical_avram_ja18i_zero_cutoff_square_integrable_transfer
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Construct a separate-space companion with the same triplet and square
moment, then transfer its law back to the ORIGINAL physical process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (t : ℝ≥0), Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2) P := by
  intro t
  obtain ⟨P₂, 𝓕₂, Y, hc, hσ, hν, hY⟩ :=
    avram_ja18j_finite_activity_countable_real_model_square X hX hFinite t
  exact avram_ja18i_zero_cutoff_square_integrable_transfer
    X Y hc hσ hν t hY
