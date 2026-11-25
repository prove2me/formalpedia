-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LSmall.sg_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:23:42.054343+00:00
-- url     : https://prove2.me/submissions/7fd5e267-53bd-4eb8-954b-fbb5e57c7c59

import Definitions.Def_Formalism_SizeWindowBrackets_SSmall
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PSmall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LSmall
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism.LFunctionChainParameters.LHost
open Formalism.FrobeniusOrbits (HostHyp HGrp hcl)
namespace Formalism.LFunctionChainParameters.LSmall
theorem _root_.solution {H : Type} [AddCommGroup H] : (0 : E0 × H) ≠ sg := by
  intro h
  have := congrArg (fun x : E0 × H => x.1.2) h
  simp [sg] at this
end Formalism.LFunctionChainParameters.LSmall
