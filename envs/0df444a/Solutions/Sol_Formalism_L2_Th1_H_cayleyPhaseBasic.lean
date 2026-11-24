-- Prove2me | solution 1 for Formalism.L2.Th1.H.cayleyPhaseBasic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:31:37.259881+00:00
-- url     : https://prove2.me/submissions/d6491375-cc4d-469f-9db6-be55f9226dae

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
import Theorems.Thm_Formalism_L2_Th1_H_ud_skew
import Theorems.Thm_Formalism_L2_Th1_H_ud_re
import Theorems.Thm_Formalism_L2_Th1_H_ud_norm
import Theorems.Thm_Formalism_L2_Th1_H_ud_phi_wd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : PhiBasic := by
  intro V _ _ H Λ α δ Ae h
  exact ⟨ud_skew h, ud_re h, fun x hx => ud_norm h hx, fun x hx y hy => ud_phi_wd h hx hy⟩
end Formalism.L2.Th1.H
