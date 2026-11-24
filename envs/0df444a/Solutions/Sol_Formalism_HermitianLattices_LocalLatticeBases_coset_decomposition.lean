-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.coset_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:44.658199+00:00
-- url     : https://prove2.me/submissions/368c36b4-4120-46a7-83a4-f4425acdbbf6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : SupportCosetStructure := by
  intro q _ n n' fW f hfW
  obtain ⟨i0, hi0⟩ : ∃ i, fW i ≠ 0 := by by_contra h; push_neg at h; exact hfW (funext h)
  have add : ∀ x y : Matrix (Fin n') (Fin n) ℤ, compF fW (x - y) = compF fW x - compF fW y := by
    intro x y; funext j; simp [compF, mul_sub, Finset.sum_sub_distrib]
  let x0 : Matrix (Fin n') (Fin n) ℤ := fun i j => if i = i0 then ((f j / fW i0 : ZMod q).val : ℤ) else 0
  have hx0 : compF fW x0 = f := by
    funext j
    simp only [compF, x0]
    rw [Finset.sum_eq_single i0]
    · simp; field_simp
    · intro i _ hi; simp [hi]
    · simp
  refine ⟨x0, ?_, ?_, ?_⟩
  · intro x; rw [add, hx0, sub_eq_zero]
  · funext j; simp [compF]
  · intro x hx l hl
    have : ∑ i, fW i * ((x.mulVec l) i : ZMod q) = ∑ j, compF fW x j * (l j : ZMod q) := by
      simp only [compF, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
    rw [this, hx]; exact hl
end Formalism.HermitianLattices.LocalLatticeBases
