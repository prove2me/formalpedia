-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_original_discounted_stopped_grid_right_atoms_le_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:20:51.526268+00:00
-- url     : https://prove2.me/submissions/723d516f-5a86-4a70-a07b-d5b7f7fdf363

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_agentB_true_original_rightdividend_grid_atoms_telescope
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false
/-- Genuine original stopped physical payment atoms are at most
the full original cumulative dividend growth over the same mesh. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s : ℕ → ℝ≥0)
    (hstrict : ∀ i, s i < s (i + 1))
    (q : ℝ) (hq : 0 ≤ q) (ρ : ℝ≥0) (m : ℕ) :
    (∑ i ∈ Finset.range m,
      if s i < ρ then
        Real.exp (-(q * (s i : ℝ))) *
          (rightLimit D (s i) ω - D (s i) ω)
      else 0) ≤ D (s m) ω - D (s 0) ω := by
  calc
    (∑ i ∈ Finset.range m,
      if s i < ρ then
        Real.exp (-(q * (s i : ℝ))) *
          (rightLimit D (s i) ω - D (s i) ω)
      else 0) ≤
      ∑ i ∈ Finset.range m,
        (rightLimit D (s i) ω - D (s i) ω) := by
      apply Finset.sum_le_sum
      intro i hi
      have hgap : 0 ≤ rightLimit D (s i) ω - D (s i) ω := by
        have hl := dividendStrategy_le_rightLimit D hD ω (s i)
        linarith
      split_ifs with hs
      · have he : Real.exp (-(q * (s i : ℝ))) ≤ 1 := by
          exact Real.exp_le_one_iff.mpr
            (neg_nonpos.mpr (mul_nonneg hq (by exact_mod_cast (s i).property)))
        nlinarith
      · exact hgap
    _ ≤ D (s m) ω - D (s 0) ω :=
      avram_agentB_true_original_rightdividend_grid_atoms_telescope
        D hD ω s hstrict m
