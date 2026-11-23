-- Prove2me | solution 1 for Formalism.L2.Th1.H.Inv.opU_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:43.475229+00:00
-- url     : https://prove2.me/submissions/66b7b957-4c90-48d5-9b3f-2ca724c4fc20

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
theorem _root_.solution {ι : Type} (H : Sesq V) (x : V) (S : Finset ι) (G : ι → V → ℂ) (z : V) :
    opU H x (fun v => ∑ i ∈ S, G i v) z = ∑ i ∈ S, opU H x (G i) z := by
  simp only [Formalism.L2.Th1.H.opU, Finset.sum_mul]
end Formalism.L2.Th1.H.Inv
