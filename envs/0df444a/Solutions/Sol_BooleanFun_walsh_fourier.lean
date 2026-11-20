-- Prove2me | solution 1 for BooleanFun.walsh_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:03:10.297329+00:00
-- url     : https://prove2.me/submissions/3bcee1fb-8ac8-4497-a0ba-0ad9ba39dda0

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution (f : BooleanFunc n) : f = ∑ S : Finset (Fin n), (𝓕 f S)•χ S := by
  convert (OrthonormalBasis.sum_repr' walsh_orthonormal_basis f).symm <;> simp; rfl
end BooleanFun
