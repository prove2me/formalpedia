-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB59_original_discounted_gaussian_mesh_noise_sup_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:58:07.537917+00:00
-- url     : https://prove2.me/submissions/337b1a85-ec35-4ef3-ae03-50e5bead9bae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB58_discounted_monotone_weighted_increment_sup_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- The original discounted physical centred Gaussian grid noise is uniformly tube-bounded. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (m : ℕ) (s : ℕ → ℝ≥0) (hs : Monotone s)
    (hs0 : s 0 = 0) (hX0 : X.X 0 ω = 0)
    (q ε : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (hTube : ∀ i ≤ m + 1,
      |X.X (s i) ω - (s i : ℝ) * X.c| ≤ ε) :
    |(Finset.range (m + 1)).sum (fun i =>
      Real.exp (-(q * (s i : ℝ))) *
        (X.X (s (i + 1)) ω - X.X (s i) ω -
          ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c))| ≤ ε := by
  let a : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
  let b : ℕ → ℝ := fun i => X.X (s i) ω - (s i : ℝ) * X.c
  have ha : Antitone a := by
    intro i j hij
    have hij' : (s i : ℝ) ≤ (s j : ℝ) := by
      exact_mod_cast hs hij
    have hmul := mul_le_mul_of_nonneg_left hij' hq
    exact Real.exp_le_exp.mpr (by nlinarith)
  have ha0 : a 0 ≤ (1 : ℝ) := by
    simp [a, hs0]
  have ham : 0 ≤ a m := le_of_lt (Real.exp_pos _)
  have hb0 : b 0 = 0 := by
    simp [b, hs0, hX0]
  have hBound : |(Finset.range (m + 1)).sum (fun i =>
      a i * (b (i + 1) - b i))| ≤ ε :=
    avram_gbB58_discounted_monotone_weighted_increment_sup_bound
      m a b ε hε ha ha0 ham hb0 (fun i hi => hTube i hi)
  have hEq :
      (Finset.range (m + 1)).sum (fun i =>
        Real.exp (-(q * (s i : ℝ))) *
          (X.X (s (i + 1)) ω - X.X (s i) ω -
            ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)) =
      (Finset.range (m + 1)).sum (fun i =>
        a i * (b (i + 1) - b i)) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a, b]
    ring
  rw [hEq]
  exact hBound
