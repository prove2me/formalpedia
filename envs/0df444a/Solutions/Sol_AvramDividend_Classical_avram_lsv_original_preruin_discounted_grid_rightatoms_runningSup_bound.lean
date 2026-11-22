-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_preruin_discounted_grid_rightatoms_runningSup_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:01:03.902073+00:00
-- url     : https://prove2.me/submissions/457515dc-4661-4e9f-b940-e15cb87582af

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_strict_preruin_right_dividends_le_initial_plus_true_Levy_runningSup
import Theorems.Thm_AvramDividend_Classical_avram_gledger87_original_strict_rightlimit_le_later_dividend
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
noncomputable section

/- Actual original dividend-strategy right atoms on a deterministic
  physical time grid stopped before ruin. A prefix induction carries both
  an unweighted cumulative payment invariant and the source running
  supremum envelope. No post-ruin dividend bound is assumed. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (s : ℕ → ℝ≥0) (hstrict : ∀ i, s i < s (i + 1))
    (m : ℕ) (hbound : ∀ i ∈ Finset.range m, s i ≤ n)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) :
    (∑ i ∈ Finset.range m,
      if s i < ρ ω then
        Real.exp (-(q * (s i : ℝ))) *
          (rightLimit D (s i) ω - D (s i) ω)
      else 0) ≤ x + runningSup X n ω := by
  classical
  let A : ℕ → ℝ := fun k =>
    ∑ i ∈ Finset.range k,
      if s i < ρ ω then
        Real.exp (-(q * (s i : ℝ))) *
          (rightLimit D (s i) ω - D (s i) ω)
      else 0
  have hSup : 0 ≤ runningSup X n ω := by
    obtain ⟨hMono, hPath⟩ := runningSup_monotone_and_path_le X ω
    have hzero : 0 ≤ runningSup X 0 ω := by
      have h := hPath 0
      rw [X.X_zero ω] at h
      exact h
    exact hzero.trans (hMono ((show (0 : ℝ≥0) ≤ n from zero_le)))
  have hMain : ∀ k : ℕ, k ≤ m →
      A k ≤ x + runningSup X n ω ∧
        (s k < ρ ω → A k ≤ D (s k) ω) := by
    intro k hk
    induction k with
    | zero =>
      have hD0 : 0 ≤ D (s 0) ω := by
        have hh := (hD.2.1 ω) ((show (0 : ℝ≥0) ≤ s 0 from zero_le))
        change D 0 ω ≤ D (s 0) ω at hh
        rw [hD.1 ω] at hh
        exact hh
      constructor
      · simpa [A] using add_nonneg hx hSup
      · intro _
        simpa [A] using hD0
    | succ k ih =>
      have hkm : k < m := Nat.lt_of_succ_le hk
      obtain ⟨hOld, hOldD⟩ := ih (Nat.le_of_lt hkm)
      have hStep : A (k + 1) = A k +
          (if s k < ρ ω then
            Real.exp (-(q * (s k : ℝ))) *
              (rightLimit D (s k) ω - D (s k) ω)
           else 0) := by
        simp only [A, Finset.sum_range_succ]
      by_cases hsk : s k < ρ ω
      · have hGap : 0 ≤ rightLimit D (s k) ω - D (s k) ω := by
          exact sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD ω (s k))
        have hExp : Real.exp (-(q * (s k : ℝ))) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          exact neg_nonpos.mpr (mul_nonneg hq (NNReal.coe_nonneg _))
        have hLe : A (k + 1) ≤ rightLimit D (s k) ω := by
          rw [hStep, if_pos hsk]
          have hCurrent := hOldD hsk
          nlinarith
        have hRuin : (s k : ℝ≥0∞) < ruinTime X x D ω := by
          exact (ENNReal.coe_lt_coe.mpr hsk).trans_le (hρruin ω)
        have hRight :=
          avram_pj_original_strict_preruin_right_dividends_le_initial_plus_true_Levy_runningSup
            X x D hD (s k) ω hRuin
        have hSupLe :=
          (runningSup_monotone_and_path_le X ω).1
            (hbound k (Finset.mem_range.mpr hkm))
        constructor
        · exact hLe.trans (hRight.trans (add_le_add_right hSupLe x))
        · intro _
          exact hLe.trans
            (avram_gledger87_original_strict_rightlimit_le_later_dividend
              D hD ω (s k) (s (k + 1)) (hstrict k))
      · have hStep0 : A (k + 1) = A k := by
          simpa [hsk] using hStep
        constructor
        · simpa only [hStep0] using hOld
        · intro hnext
          exact False.elim (hsk ((hstrict k).trans hnext))
  exact (hMain m le_rfl).1

