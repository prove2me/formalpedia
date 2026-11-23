-- Prove2me | solution 1 for Formalism.L2.DIV.weightMet_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:00.333805+00:00
-- url     : https://prove2.me/submissions/2243bea4-bde2-4148-9ef1-a4dfb6c48a29

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] {n : ℕ} {Ix : Type} [Fintype Ix]
namespace Formalism.L2.DIV
theorem _root_.solution (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (weightMet pr t X v).mulVec y =
      ∑ p, ((t p v : ℝ) : ℂ) * (star (((pr p).map v.embedding).mulVec x) ⬝ᵥ
        (metOf (X v)).mulVec (((pr p).map v.embedding).mulVec y)) := by
  rw [weightMet, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, restrMetC, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
end Formalism.L2.DIV
