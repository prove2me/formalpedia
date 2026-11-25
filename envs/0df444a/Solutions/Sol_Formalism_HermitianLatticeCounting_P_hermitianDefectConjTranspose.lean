-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hermitianDefectConjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:05:45.887261+00:00
-- url     : https://prove2.me/submissions/73f67b94-0c16-4eb1-9beb-21c853398afa

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : PhiInverse := by
  intro n R _ _ _ _ S Y hS hD
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.Phi at *
  have e1 : (1 + S * Yᴴ) * (1 + S * Y) = 1 := by
    have : (1 + S * Yᴴ) * (1 + S * Y) = 1 + S * (Y + Yᴴ + Yᴴ * S * Y) := by noncomm_ring
    rw [this, hD, Matrix.mul_zero, add_zero]
  have e2 : (1 + S * Y) * (1 + S * Yᴴ) = 1 := by
    rw [← Matrix.inv_eq_right_inv e1]
    exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse e1)
  have e3 : S * (Yᴴ + Y + Y * S * Yᴴ) = 0 := by
    have : S * (Yᴴ + Y + Y * S * Yᴴ) = (1 + S * Y) * (1 + S * Yᴴ) - 1 := by noncomm_ring
    rw [this, e2, sub_self]
  have key : Yᴴ + Y + Y * S * Yᴴ =
      (Y + Yᴴ + Yᴴ * S * Y) * (1 + S * Yᴴ) - Yᴴ * (S * (Yᴴ + Y + Y * S * Yᴴ)) := by
    noncomm_ring
  rw [Matrix.conjTranspose_conjTranspose, key, hD, e3]
  simp
end Formalism.HermitianLatticeCounting.P
