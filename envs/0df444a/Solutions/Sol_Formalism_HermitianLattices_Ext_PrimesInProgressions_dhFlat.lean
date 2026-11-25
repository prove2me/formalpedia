-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhFlat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:17:21.535231+00:00
-- url     : https://prove2.me/submissions/f3199491-148c-4bc3-b0fa-461380f373f8

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (S : Multiset ℂ) : ∃ (N : ℕ) (w : Fin N → ℂ), Finset.univ.val.map w = S := by
  refine ⟨S.toList.length, S.toList.get, ?_⟩
  rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
