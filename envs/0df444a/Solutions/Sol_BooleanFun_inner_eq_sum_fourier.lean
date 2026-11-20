-- Prove2me | solution 1 for BooleanFun.inner_eq_sum_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:04:37.715367+00:00
-- url     : https://prove2.me/submissions/5c322d4b-ab3b-4e2c-ad46-9139eee3b1df

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_fourier_eq_inner

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution : ⟪f, g⟫ = ∑ S : Finset (Fin n), (𝓕 f S) * (𝓕 g S) := by
  rw [← walsh_orthonormal_basis.sum_inner_mul_inner f g]
  apply Finset.sum_congr rfl
  intro S _
  rw [walsh_orthonormal_basis_apply S, real_inner_comm (χ S) f,
    ← fourier_eq_inner (f := f) (S := S),
    ← fourier_eq_inner (f := g) (S := S)]
end BooleanFun
