-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.modulus_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T09:58:23.892533+00:00
-- url     : https://prove2.me/submissions/0acd130d-c652-4eef-a56c-602f640e3ff3

-- Generated from ChapterWignerSymmetry.lean — solution of BookProof.ChapterWignerSymmetry.modulus_add
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
import Theorems.Thm_BookProof_ChapterWignerSymmetry_sum_pair_prime
import Theorems.Thm_BookProof_ChapterWignerSymmetry_S_zero
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
theorem solution (hS : WignerCoord S o) {i : ι} (hi : i ≠ o) (v : ι → ℂ) :
    ‖S v o + S v i‖ = ‖v o + v i‖ := by

  set u := pairCoord o i with hu
  have huo : u o = 1 := by simp [hu, pairCoord]
  have hui : u i = 1 := by simp [hu, pairCoord, hi]
  have huk : ∀ k, k ≠ o → k ≠ i → u k = 0 := by
    intro k h1 h2; simp [hu, pairCoord, h1, h2]
  have hSu : ∀ k, k ≠ o → k ≠ i → S u k = 0 := fun k h1 h2 => S_zero hS (huk k h1 h2)
  have h := hS.inner_norm v u
  rw [sum_pair_prime hi hSu, sum_pair_prime hi huk] at h
  rw [hS.normalized i hi] at h
  have hnorm : ‖S u i‖ = 1 := by rw [hS.coord_norm u i, hui]; simp
  rw [huo, hui] at h
  rw [show conj (S v o) * S u i + conj (S v i) * S u i
        = (conj (S v o) + conj (S v i)) * S u i by ring] at h
  rw [norm_mul, hnorm, mul_one, mul_one, mul_one, ← map_add, ← map_add,
    Complex.norm_conj, Complex.norm_conj] at h
  exact h
