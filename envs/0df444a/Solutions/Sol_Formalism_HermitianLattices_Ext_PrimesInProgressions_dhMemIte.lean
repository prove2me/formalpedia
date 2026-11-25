-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhMemIte
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:59:54.705858+00:00
-- url     : https://prove2.me/submissions/2643bfe5-be80-4d95-9727-8d722abd1e78

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqB

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
theorem _root_.solution (F : Multiset ℂ) (c : Prop) [Decidable c] (b x : ℂ) (h : x ∈ (if c then F.erase b else F)) :
    x ∈ F := by
  split_ifs at h
  · exact Multiset.mem_of_mem_erase h
  · exact h
end Formalism.HermitianLattices.Ext.PrimesInProgressions
