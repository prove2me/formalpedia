-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_jumpfree_path_largeband_integral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T18:17:44.029657+00:00
-- url     : https://prove2.me/submissions/bfc8dd0a-2082-479f-8ecd-07f8eaa98510

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_truly_jumpless_large_mark_sum_identically_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A jumpfree physical original Lévy path has no marked large-jump source atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hNoJump : ∀ u : ℝ≥0, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0)
    (t : ℝ≥0) :
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω = 0 := by
  exact avram_a22_original_truly_jumpless_large_mark_sum_identically_zero
    X ω hNoJump t
