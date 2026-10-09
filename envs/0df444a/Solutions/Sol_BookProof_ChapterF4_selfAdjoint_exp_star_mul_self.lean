-- Prove2me | solution 1 for BookProof.ChapterF4.selfAdjoint_exp_star_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:01:46.426697+00:00
-- url     : https://prove2.me/submissions/762259f2-7cd4-4507-8f07-ee461c5c1dd7

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.selfAdjoint_exp_star_mul_self
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

set_option maxHeartbeats 1000000 in
theorem solution (h : selfAdjoint A) :
    star ((selfAdjoint.expUnitary h : A)) * (selfAdjoint.expUnitary h : A) = 1 := by

  exact Unitary.coe_star_mul_self (selfAdjoint.expUnitary h)
