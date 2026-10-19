-- Prove2me | solution 1 for BookProof.FriedrichsSquare.adjPairs_factorRel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:10:34.280987+00:00
-- url     : https://prove2.me/submissions/fe6bd8e2-f022-4f64-947b-ba79525a1860

-- Generated from ChapterFriedrichsSquareFactorization.lean — solution of BookProof.FriedrichsSquare.adjPairs_factorRel
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Theorems.Thm_BookProof_FriedrichsSquare_exists_mem_factorRel_add
import Theorems.Thm_BookProof_FriedrichsSquare_factorRel_le_adjPairs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterClosureUniqueness
open BookProof.FriedrichsSquare




open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness
open BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace F] (A : D →ₗ[ℂ] F) :
    adjPairs (factorRel A) = factorRel A := by

  refine le_antisymm ?_ (factorRel_le_adjPairs A)
  intro p hp
  obtain ⟨r, hr, hrsum⟩ := exists_mem_factorRel_add A (p.1 + p.2)
  have hr' : r ∈ adjPairs (factorRel A) := factorRel_le_adjPairs A hr
  have hv : p - r ∈ adjPairs (factorRel A) := (adjPairs (factorRel A)).sub_mem hp hr'
  have hvsum : (p - r).1 + (p - r).2 = 0 := by
    have hsplit : (p - r).1 + (p - r).2 = (p.1 + p.2) - (r.1 + r.2) := by
      simp only [Prod.fst_sub, Prod.snd_sub]; abel
    rw [hsplit, hrsum, sub_self]
  have key : ∀ x : F, (inner ℂ x (p - r).1 : ℂ) = 0 := by
    intro x
    obtain ⟨q, hq, hqsum⟩ := exists_mem_factorRel_add A x
    have hqv := hv q hq
    have hzero : (inner ℂ q.1 ((p - r).1 + (p - r).2) : ℂ) = 0 := by rw [hvsum]; simp
    rw [inner_add_right] at hzero
    rw [← hqsum, inner_add_left, hqv]
    linear_combination hzero
  have hv1 : (p - r).1 = 0 := by
    have := key (p - r).1
    exact inner_self_eq_zero.1 this
  have hv2 : (p - r).2 = 0 := by
    have := hvsum
    rw [hv1, zero_add] at this
    exact this
  have hpr : p = r := by
    have h1 : p.1 = r.1 := by
      have := hv1
      simp only [Prod.fst_sub, sub_eq_zero] at this
      exact this
    have h2 : p.2 = r.2 := by
      have := hv2
      simp only [Prod.snd_sub, sub_eq_zero] at this
      exact this
    exact Prod.ext h1 h2
  rw [hpr]
  exact hr
