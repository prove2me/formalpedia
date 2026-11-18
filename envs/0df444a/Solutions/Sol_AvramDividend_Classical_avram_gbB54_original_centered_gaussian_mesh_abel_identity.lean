-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54_original_centered_gaussian_mesh_abel_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:41:52.661404+00:00
-- url     : https://prove2.me/submissions/b4f5d737-b6a0-49b4-ad0d-ecdc4672d189

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB53_physical_discounted_mesh_abel_telescope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Discounted original centred Gaussian physical increments satisfy Abel summation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (ω : Ω) (m : ℕ) (s : ℕ → ℝ≥0) :
    let a : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
    let b : ℕ → ℝ := fun i => X.X (s i) ω - (s i : ℝ) * X.c
    (Finset.range (m + 1)).sum (fun i =>
      a i * (X.X (s (i + 1)) ω - X.X (s i) ω -
        ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)) =
    a m * b (m + 1) - a 0 * b 0 +
      (Finset.range m).sum (fun i =>
        (a i - a (i + 1)) * b (i + 1)) := by
  dsimp
  have hZ (i : ℕ) :
      X.X (s (i + 1)) ω - X.X (s i) ω -
          ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c =
      (X.X (s (i + 1)) ω - (s (i + 1) : ℝ) * X.c) -
        (X.X (s i) ω - (s i : ℝ) * X.c) := by
    ring
  simp_rw [hZ]
  exact avram_gbB53_physical_discounted_mesh_abel_telescope m
    (fun i => Real.exp (-(q * (s i : ℝ))))
    (fun i => X.X (s i) ω - (s i : ℝ) * X.c)
