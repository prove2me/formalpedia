-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.key_global
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:55:09.135564+00:00
-- url     : https://prove2.me/submissions/9dd84259-8a94-4bb5-886d-ce0dea76262a

-- Generated from ChapterWignerSymmetry.lean — solution of BookProof.ChapterWignerSymmetry.key_global
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
import Theorems.Thm_BookProof_ChapterWignerSymmetry_key_index
import Theorems.Thm_BookProof_ChapterWignerSymmetry_key_consistent
open BookProof.ChapterWignerSymmetry



open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {T : E → E}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

set_option maxHeartbeats 1000000 in
theorem solution (hS : WignerCoord S o) :
    (∀ i, i ≠ o → ∀ v, conj (S v o) * S v i = conj (v o) * v i) ∨
    (∀ i, i ≠ o → ∀ v, conj (S v o) * S v i = conj (conj (v o) * v i)) := by

  by_cases hex : ∃ i, i ≠ o ∧ ∀ v, conj (S v o) * S v i = conj (v o) * v i
  · obtain ⟨i₀, hi₀, hkey₀⟩ := hex
    left
    intro j hj v
    rcases key_index hS hj with h | h
    · exact h v
    · by_cases hji : j = i₀
      · subst hji; exact hkey₀ v
      · exact (key_consistent hS hi₀ hj (fun e => hji e.symm) hkey₀ h).elim
  · push_neg at hex
    right
    intro i hi v
    rcases key_index hS hi with h | h
    · obtain ⟨v₀, hv₀⟩ := hex i hi
      exact absurd (h v₀) hv₀
    · exact h v
