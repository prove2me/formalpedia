-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.key_index
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T09:58:26.370967+00:00
-- url     : https://prove2.me/submissions/9ce53f5c-ac1f-4936-85f5-0e459e11914d

-- Generated from ChapterWignerSymmetry.lean — solution of BookProof.ChapterWignerSymmetry.key_index
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
import Theorems.Thm_BookProof_ChapterWignerSymmetry_key_complex
import Theorems.Thm_BookProof_ChapterWignerSymmetry_key_complex_prime
import Theorems.Thm_BookProof_ChapterWignerSymmetry_modulus_add
import Theorems.Thm_BookProof_ChapterWignerSymmetry_exists_zeta
import Definitions.Def_ChapterWignerSymmetryInfinite
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
theorem solution (hS : WignerCoord S o) {i : ι} (hi : i ≠ o) :
    (∀ v, conj (S v o) * S v i = conj (v o) * v i) ∨
    (∀ v, conj (S v o) * S v i = conj (conj (v o) * v i)) := by

  obtain ⟨ζ, hζ, hrel⟩ := exists_zeta hS hi
  rcases hζ with hζ | hζ
  · left
    intro v
    have h1 : ‖S v o‖ = ‖v o‖ := hS.coord_norm v o
    have h2 : ‖S v i‖ = ‖v i‖ := hS.coord_norm v i
    have h3 : ‖S v o + S v i‖ = ‖v o + v i‖ := modulus_add hS hi v
    have h4 := hrel v
    rw [hζ] at h4
    exact key_complex (S v o) (S v i) (v o) (v i) h1 h2 h3 h4
  · right
    intro v
    have h1 : ‖S v o‖ = ‖v o‖ := hS.coord_norm v o
    have h2 : ‖S v i‖ = ‖v i‖ := hS.coord_norm v i
    have h3 : ‖S v o + S v i‖ = ‖v o + v i‖ := modulus_add hS hi v
    have h4 := hrel v
    rw [hζ] at h4
    exact key_complex_prime (S v o) (S v i) (v o) (v i) h1 h2 h3 h4
