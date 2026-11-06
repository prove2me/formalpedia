-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_predividend_finiteband_reserve_exact_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:44:42.581587+00:00
-- url     : https://prove2.me/submissions/60726ebf-032d-4786-be2f-332bfa245836

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_controlled_finiteband_reserve_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

/-- Physical finite-band source before the next dividend atom, on the original Levy path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let E : Set (ℝ≥0 × ℝ) :=
      Ioc (0 : ℝ≥0) t ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    riskProcess X x D t ω -
      (rightLimit D t ω - D t ω) =
      x + (t : ℝ) * X.c +
        ((∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
            E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0) -
          (t : ℝ) * (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
        rightLimit D t ω := by
  dsimp only
  have hband :=
    avram_p4_f_assembly_original_controlled_finiteband_reserve_identity
      X x D n t ω
  dsimp only at hband
  linarith
