-- Prove2me | solution 1 for BookProof.FriedrichsSquare.mem_flipGraph_orthogonal_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:10:03.623481+00:00
-- url     : https://prove2.me/submissions/6632a85e-20c4-4086-bc38-cf0f4cf4ce5e

-- Generated from ChapterFriedrichsSquareFactorization.lean — solution of BookProof.FriedrichsSquare.mem_flipGraph_orthogonal_iff
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Theorems.Thm_BookProof_FriedrichsSquare_mem_flipGraph_iff
import Theorems.Thm_BookProof_ClosureUniqueness_adjGraph_eq_adjPairs_clGraph
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.FriedrichsSquare




open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness
open BookProof.ClosureUniqueness
open BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {A : D →ₗ[ℂ] F} {q : WithLp 2 (F × F)} :
    q ∈ (flipGraph A)ᗮ ↔ WithLp.ofLp q ∈ adjGraph A := by

  rw [adjGraph_eq_adjPairs_clGraph, Submodule.mem_orthogonal]
  constructor
  · intro hq r hr
    have hmem : WithLp.toLp 2 (-r.2, r.1) ∈ flipGraph A := by
      rw [mem_flipGraph_iff]
      simpa using hr
    have h0 := hq _ hmem
    rw [WithLp.prod_inner_apply] at h0
    simp only [inner_neg_left] at h0
    linear_combination -h0
  · intro hq u hu
    have hr : ((WithLp.ofLp u).2, -(WithLp.ofLp u).1) ∈ clGraph A := hu
    have h := hq _ hr
    simp only [inner_neg_left] at h
    rw [WithLp.prod_inner_apply]
    linear_combination -h
