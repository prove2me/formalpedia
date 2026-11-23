-- Prove2me | solution 1 for FracRiccati.Radius.Supplement.theorem_6_1_b_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T21:10:22.540791+00:00
-- url     : https://prove2.me/submissions/c8909251-dc99-4522-9231-fb91e95f4a5f

import Mathlib
import Definitions.Def_FracRiccati_Radius_Supplement_DoubleSeries
namespace FracRiccati.Radius.Supplement

/-- At a regular Gamma input, the claimed valuation lower bound fails. -/
lemma fr_g3 : Real.Gamma 3 = 2 := by
  rw [show (3:ℝ) = (2:ℕ)+1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num [Nat.factorial]
lemma fr_c10 : doubleCoeff 2 1 1 1 1 1 1 0 = 1/2 := by
  rw [doubleCoeff]; norm_num [fr_g3]
lemma fr_c11 : doubleCoeff 2 1 1 1 1 1 1 1 = 1 := by
  rw [doubleCoeff]; norm_num
lemma fr_c12 : doubleCoeff 2 1 1 1 1 1 1 2 = 1 := by
  rw [doubleCoeff]; norm_num
lemma fr_c1 (k : ℕ) : doubleCoeff 2 1 1 1 1 1 1 (k+3) = 0 := by
  rw [doubleCoeff]
lemma fr_rec (j ℓ : ℕ) : doubleCoeff 2 1 1 1 1 1 (j+2) ℓ = ((1:ℂ) * doubleCoeff 2 1 1 1 1 1 (j+1) ℓ + 1 * ∑ i ∈ Finset.Ico 1 (j+1), ∑ r ∈ Finset.range (ℓ+1), doubleCoeff 2 1 1 1 1 1 i r * doubleCoeff 2 1 1 1 1 1 (j+1-i) (ℓ-r)) * ((Real.Gamma (2 * (j+1:ℕ) - (ℓ:ℝ) + 1) / Real.Gamma (2 * (j+2:ℕ) - (ℓ:ℝ) + 1) : ℝ) : ℂ) := by
  rw [doubleCoeff, Finset.sum_attach (Finset.Ico 1 (j+1)) (fun i => ∑ r ∈ Finset.range (ℓ+1), doubleCoeff 2 1 1 1 1 1 i r * doubleCoeff 2 1 1 1 1 1 (j+1-i) (ℓ-r))]
lemma fr_c24 : doubleCoeff 2 1 1 1 1 1 2 4 = 0 := by
  rw [fr_rec 0 4]; simp [fr_c1 1]
lemma fr_c34 : doubleCoeff 2 1 1 1 1 1 3 4 = 1/2 := by
  rw [fr_rec 1 4, fr_c24, Nat.Ico_succ_singleton]
  simp [Finset.sum_range_succ, fr_c10, fr_c11, fr_c12, fr_c1 0, fr_c1 1]
  norm_num [fr_g3]

theorem theorem_6_1_b_counterexample :
    let a := doubleCoeff 2 1 1 1 1 1
    a 1 4 = 0 ∧ a 2 4 = 0 ∧ a 3 4 = (1 / 2 : ℂ) ∧
    valuation a 4 = (3 : ℕ∞) ∧
    ¬ ((1 + (4 - 1) : ℕ) : ℕ∞) ≤ valuation a 4 := by
  intro a
  have h14 : a 1 4 = 0 := fr_c1 1
  have h24 : a 2 4 = 0 := fr_c24
  have h34 : a 3 4 = 1/2 := fr_c34
  have hv : valuation a 4 = (3 : ℕ∞) := by
    unfold valuation
    apply le_antisymm
    · exact sInf_le ⟨3, by norm_num, by rw [h34]; norm_num, rfl⟩
    · apply le_sInf
      rintro k ⟨n, hn, hne, rfl⟩
      have : 3 ≤ n := by
        by_contra h
        interval_cases n
        · exact hne h14
        · exact hne h24
      exact_mod_cast this
  refine ⟨h14, h24, h34, hv, ?_⟩
  rw [hv]; decide


end FracRiccati.Radius.Supplement

open FracRiccati.Radius.Supplement in
theorem solution :
    let a := doubleCoeff 2 1 1 1 1 1
    a 1 4 = 0 ∧ a 2 4 = 0 ∧ a 3 4 = (1 / 2 : ℂ) ∧
    valuation a 4 = (3 : ℕ∞) ∧
    ¬ ((1 + (4 - 1) : ℕ) : ℕ∞) ≤ valuation a 4 := by
  intro a
  have h14 : a 1 4 = 0 := fr_c1 1
  have h24 : a 2 4 = 0 := fr_c24
  have h34 : a 3 4 = 1/2 := fr_c34
  have hv : valuation a 4 = (3 : ℕ∞) := by
    unfold valuation
    apply le_antisymm
    · exact sInf_le ⟨3, by norm_num, by rw [h34]; norm_num, rfl⟩
    · apply le_sInf
      rintro k ⟨n, hn, hne, rfl⟩
      have : 3 ≤ n := by
        by_contra h
        interval_cases n
        · exact hne h14
        · exact hne h24
      exact_mod_cast this
  refine ⟨h14, h24, h34, hv, ?_⟩
  rw [hv]; decide

