-- Prove2me | solution 1 for Formalism.L2.DIV.metOfSpec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:39.1711+00:00
-- url     : https://prove2.me/submissions/e0ab1da8-230e-40eb-9012-d4c096d7b4bf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_L2_DIV_frameOfSpec

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
namespace Formalism.L2.DIV
theorem _root_.solution : MetOfSpec := by
  intro n Y hY
  have hpos : (metOf Y).PosDef := by
    apply Matrix.PosDef.conjTranspose_mul_self
    exact Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _ hY))
  refine ⟨hpos, ?_, (frameOfSpec n _ hpos).2⟩
  apply Matrix.inv_eq_right_inv
  rw [metOf, Matrix.mul_assoc, ← Matrix.mul_assoc Y⁻¹, Matrix.nonsing_inv_mul _ hY, Matrix.one_mul,
    ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hY, Matrix.conjTranspose_one]
end Formalism.L2.DIV
