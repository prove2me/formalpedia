-- Prove2me | solution 1 for Formalism.L2.Th1.H.Inv.altE_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:17.354413+00:00
-- url     : https://prove2.me/submissions/c4151cbf-7ae6-4338-8320-abb4b9afea74

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence

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
open Formalism.L2.Th1.H.Inv
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H.Inv
theorem _root_.solution (H : Sesq V) (x x' y : V) : altE H (x + x') y = altE H x y + altE H x' y := by
  simp only [Formalism.L2.Th1.H.altE, map_add, LinearMap.add_apply, Complex.add_im]
end Formalism.L2.Th1.H.Inv
