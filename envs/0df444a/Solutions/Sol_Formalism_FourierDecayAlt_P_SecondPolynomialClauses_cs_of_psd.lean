-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SecondPolynomialClauses.cs_of_psd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:57.696272+00:00
-- url     : https://prove2.me/submissions/69bb951d-7c33-4d35-a69c-f57a38da3d58

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_herm_of_psd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SecondPolynomialClauses
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.SecondPolynomialClauses
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (R : Formalism.FourierDecayAlt.F7.Sesq V) (hR : PSD R)
    (x y : V) : ‖R x y‖ ^ 2 ≤ (R x x).re * (R y y).re := by
  let c : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => R y x
      conj_inner_symm := fun x y => herm_of_psd R hR x y
      re_inner_nonneg := fun x => (hR x).2
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ V _ _ _ c x y
  have e : ‖R y x‖ = ‖R x y‖ := by rw [← herm_of_psd R hR x y, Complex.norm_conj]
  rw [sq]
  calc ‖R x y‖ * ‖R x y‖ = ‖R y x‖ * ‖R x y‖ := by rw [e]
    _ ≤ _ := h
end Formalism.FourierDecayAlt.P.SecondPolynomialClauses
