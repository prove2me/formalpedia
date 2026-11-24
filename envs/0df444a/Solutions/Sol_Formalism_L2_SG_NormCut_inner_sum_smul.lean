-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.inner_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:27.667454+00:00
-- url     : https://prove2.me/submissions/011e333e-6f33-4406-b547-e8d268b67ec6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormAsm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut
variable {I : Type*} [Group I] [Fintype I]
namespace Formalism.L2.SG.NormCut
theorem _root_.solution {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (c : I → ℂ) (Z : I → K) :
    inner ℂ (∑ i, c i • Z i) (∑ j, c j • Z j) = ∑ i, ∑ j, conj (c i) * c j * inner ℂ (Z i) (Z j) := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right]
  ring
end Formalism.L2.SG.NormCut
