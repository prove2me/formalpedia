-- Prove2me | solution 1 for Formalism.L2.Th1.H.Inv.inter_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:34.960844+00:00
-- url     : https://prove2.me/submissions/88aaba10-7df4-4162-947d-c2dd3fad22f9

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
theorem _root_.solution (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ : AddSubgroup V) :
    inter H α Λ₁ Λ₂ 0 = 0 := by
  funext z
  simp [Formalism.L2.Th1.H.inter, Formalism.L2.Th1.H.opU]
end Formalism.L2.Th1.H.Inv
