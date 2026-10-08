-- Prove2me | solution 1 for BookProof.ChapterAbelianAtomicCondensation.diagonal_starAlgebra_package
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:56:42.212985+00:00
-- url     : https://prove2.me/submissions/ce2aca73-8c20-47f2-a926-f8b1c8b6818b

-- Generated from ChapterAbelianAtomicCondensation.lean — theorem BookProof.ChapterAbelianAtomicCondensation.diagonal_starAlgebra_package
import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianAtomicCondensation


open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable

namespace BookProof.ChapterAbelianDiagonalCountable
@[simp] theorem diagOp_apply (d : EllInf) (f : Ell2C) (i : ℕ) :
    ((diagOp d f : Ell2C) : ℕ → ℂ) i = (d : ℕ → ℂ) i * (f : ℕ → ℂ) i := rfl

theorem diagOp_mul (d e : EllInf) : diagOp (d * e) = (diagOp d).comp (diagOp e) := by
  ext f i
  simp [mul_assoc]

theorem diagOp_one : diagOp (1 : EllInf) = ContinuousLinearMap.id ℂ Ell2C := by
  ext f i
  simp

theorem diagOp_star (d : EllInf) (f g : Ell2C) :
    (inner ℂ (diagOp d f) g : ℂ) = inner ℂ f (diagOp (star d) g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  simp [RCLike.inner_apply, map_mul, mul_comm, mul_left_comm]

theorem diagOp_injective : Function.Injective diagOp := by
  intro d e h
  apply lp.ext
  funext i
  have := congrArg (fun T => ((T (lp.single 2 i (1 : ℂ)) : Ell2C) : ℕ → ℂ) i) h
  simpa using this
end BookProof.ChapterAbelianDiagonalCountable

theorem solution :
    Function.Injective diagOp ∧
      (∀ d e : EllInf, diagOp (d * e) = (diagOp d).comp (diagOp e)) ∧
      diagOp (1 : EllInf) = ContinuousLinearMap.id ℂ Ell2C ∧
      (∀ d : EllInf, ∀ f g : Ell2C,
        (inner ℂ (diagOp d f) g : ℂ) = (inner ℂ f (diagOp (star d) g) : ℂ)) :=
  ⟨diagOp_injective, diagOp_mul, diagOp_one, diagOp_star⟩

#print axioms solution

