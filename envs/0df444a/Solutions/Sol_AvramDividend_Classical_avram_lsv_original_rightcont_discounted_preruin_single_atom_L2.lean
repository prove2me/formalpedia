-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_rightcont_discounted_preruin_single_atom_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:12:34.778381+00:00
-- url     : https://prove2.me/submissions/70d8db7b-0b55-4756-8e30-06fa77788c3c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_rightatoms_expected_mass_L1
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_rightatoms_square_L1
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : 0 < X.σ)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n s : ℝ≥0) (hsn : s ≤ n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q) :
    let H : Ω → ℝ := fun ω =>
      if s < ρ ω then
        Real.exp (-(q * (s : ℝ))) *
          (rightLimit D s ω - D s ω)
      else 0
    Measurable[𝓕.rightCont s] H ∧
      Integrable H P ∧
      Integrable (fun ω => (H ω)^2) P ∧
      (∀ ω, 0 ≤ H ω) := by
  classical
  let H : Ω → ℝ := fun ω =>
    if s < ρ ω then
      Real.exp (-(q * (s : ℝ))) *
        (rightLimit D s ω - D s ω)
    else 0
  let grid : ℕ → ℝ≥0 := fun i => s + (i : ℝ≥0)
  have hstrict : ∀ i, grid i < grid (i + 1) := by
    intro i
    dsimp [grid]
    have hi : (i : ℝ≥0) < ((i + 1 : ℕ) : ℝ≥0) := by
      exact_mod_cast Nat.lt_succ_self i
    calc
      s + (i : ℝ≥0) = (i : ℝ≥0) + s := add_comm _ _
      _ < ((i + 1 : ℕ) : ℝ≥0) + s := add_lt_add_left hi s
      _ = s + ((i + 1 : ℕ) : ℝ≥0) := add_comm _ _
  have hbound : ∀ i ∈ Finset.range 1, grid i ≤ n := by
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst i
    simpa [grid] using hsn
  have hA : Integrable H P := by
    have hI := (avram_lsv_original_preruin_discounted_rightatoms_expected_mass_L1
      X hσ x hx D hD n ρ hρstop hρruin grid hstrict 1
      hbound q hq).1
    simpa [grid, H, Finset.sum_range_one] using hI
  have hA2 : Integrable (fun ω => (H ω)^2) P := by
    have hI := (avram_lsv_original_preruin_discounted_rightatoms_square_L1
      X hBV hσ x hx D hD n ρ hρstop hρruin grid hstrict 1
      hbound q hq).1
    simpa [grid, H, Finset.sum_range_one] using hI
  have hMeas : Measurable[𝓕.rightCont s] H := by
    have hR : Measurable[𝓕.rightCont s] (rightLimit D s) :=
      (dividendStrategy_rightLimit_adapted_rightCont D hD) s
    have hDmeas : Measurable[𝓕.rightCont s] (D s) :=
      (hD.2.2.2 s).mono (𝓕.le_rightCont s) le_rfl
    have hEvent : MeasurableSet[𝓕.rightCont s] {ω : Ω | s < ρ ω} := by
      have hs := hρstop s
      have he : {ω : Ω | s < ρ ω} =
          {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤ s}ᶜ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, WithTop.coe_le_coe,
          not_le]
      rw [he]
      exact hs.compl
    exact Measurable.ite hEvent
      (measurable_const.mul (hR.sub hDmeas)) measurable_const
  refine ⟨hMeas, hA, hA2, ?_⟩
  intro ω
  dsimp [H]
  by_cases h : s < ρ ω
  · simp only [if_pos h]
    exact mul_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr
      (dividendStrategy_le_rightLimit D hD ω s))
  · simp [h]

