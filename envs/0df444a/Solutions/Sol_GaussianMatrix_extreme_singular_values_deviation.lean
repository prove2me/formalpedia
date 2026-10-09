-- Prove2me | solution 1 for GaussianMatrix.extreme_singular_values_deviation
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:29:03.332303+00:00
-- url     : https://prove2.me/submissions/eb44a4af-7c86-4190-baf9-313a819af22d

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_gordon
import Theorems.Thm_GaussianMatrix_gaussian_concentration
import Theorems.Thm_GaussianMatrix_sMin_lipschitz
import Theorems.Thm_GaussianMatrix_specNorm_lipschitz

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- Lower tail of `σ_min` (no aspect-ratio hypothesis needed). -/
lemma esvd_sMin_tail {N n : ℕ} (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    (gaussianMatrix N n) {A | sMin (Matrix.of A) ≤ Real.sqrt N - Real.sqrt n - t}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
  set h : (Fin N → Fin n → ℝ) → ℝ := fun X => -sMin (Matrix.of X) with hh
  have hLip : ∀ X Y, |h X - h Y| ≤ 1 * frobNorm (Matrix.of X - Matrix.of Y) := by
    intro X Y
    have := sMin_lipschitz (Matrix.of X) (Matrix.of Y)
    simp only [hh, one_mul]
    rw [show -sMin (Matrix.of X) - -sMin (Matrix.of Y)
        = -(sMin (Matrix.of X) - sMin (Matrix.of Y)) by ring, abs_neg]
    exact this
  obtain ⟨-, hconc⟩ := gaussian_concentration h 1 one_pos hLip t ht
  obtain ⟨-, -, hmean, -, -⟩ := gordon (N := N) hn
  have hint : ∫ Y, h Y ∂(gaussianMatrix N n) = -∫ Y, sMin (Matrix.of Y) ∂(gaussianMatrix N n) := by
    simp only [hh]
    exact integral_neg _
  refine le_trans (measure_mono ?_) hconc
  intro X hX
  simp only [Set.mem_ofPred_eq] at hX ⊢
  rw [hint]
  simp only [hh]
  linarith

/-- Upper tail of the spectral norm. -/
lemma esvd_specNorm_tail {N n : ℕ} (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    (gaussianMatrix N n) {A | Real.sqrt N + Real.sqrt n + t ≤ specNorm (Matrix.of A)}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
  set h : (Fin N → Fin n → ℝ) → ℝ := fun X => specNorm (Matrix.of X) with hh
  have hLip : ∀ X Y, |h X - h Y| ≤ 1 * frobNorm (Matrix.of X - Matrix.of Y) := by
    intro X Y
    simp only [hh, one_mul]
    exact specNorm_lipschitz (Matrix.of X) (Matrix.of Y)
  obtain ⟨-, hconc⟩ := gaussian_concentration h 1 one_pos hLip t ht
  obtain ⟨-, -, -, -, hmean⟩ := gordon (N := N) hn
  refine le_trans (measure_mono ?_) hconc
  intro X hX
  simp only [Set.mem_ofPred_eq, hh] at hX ⊢
  linarith

end GaussianMatrix

open GaussianMatrix

theorem solution {N n : ℕ} (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    1 - ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2))
      ≤ (gaussianMatrix N n) {A | Real.sqrt N - Real.sqrt n - t ≤ sMin (Matrix.of A) ∧
          specNorm (Matrix.of A) ≤ Real.sqrt N + Real.sqrt n + t} := by
  set μ := gaussianMatrix N n
  set E := {A : Fin N → Fin n → ℝ | Real.sqrt N - Real.sqrt n - t ≤ sMin (Matrix.of A) ∧
          specNorm (Matrix.of A) ≤ Real.sqrt N + Real.sqrt n + t} with hE
  set S1 := {A : Fin N → Fin n → ℝ | sMin (Matrix.of A) ≤ Real.sqrt N - Real.sqrt n - t}
  set S2 := {A : Fin N → Fin n → ℝ | Real.sqrt N + Real.sqrt n + t ≤ specNorm (Matrix.of A)}
  have hsub : Eᶜ ⊆ S1 ∪ S2 := by
    intro X hX
    simp only [hE, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_le] at hX
    rcases hX with hX | hX
    · exact Or.inl (le_of_lt hX)
    · exact Or.inr (le_of_lt hX)
  have hc : μ Eᶜ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := by
    have hpos : 0 ≤ Real.exp (-t ^ 2 / 2) := (Real.exp_pos _).le
    rw [two_mul, ENNReal.ofReal_add hpos hpos]
    calc μ Eᶜ ≤ μ (S1 ∪ S2) := measure_mono hsub
      _ ≤ μ S1 + μ S2 := measure_union_le _ _
      _ ≤ _ := add_le_add (esvd_sMin_tail hn t ht) (esvd_specNorm_tail hn t ht)
  have h1 : (1 : ENNReal) ≤ μ E + μ Eᶜ := by
    calc (1 : ENNReal) = μ Set.univ := measure_univ.symm
      _ = μ (E ∪ Eᶜ) := by rw [Set.union_compl_self]
      _ ≤ μ E + μ Eᶜ := measure_union_le _ _
  rw [tsub_le_iff_right]
  exact h1.trans (add_le_add le_rfl hc)
