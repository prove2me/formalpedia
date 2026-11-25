-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.extension_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:14:02.121167+00:00
-- url     : https://prove2.me/submissions/35f94305-a880-4bc3-91ac-06f8475e0b88

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_unram
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_inertia_two
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_inertia_q
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_inertia_d
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_frob_two
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_frob_q
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_frob_d

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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LHost
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
open Formalism.FrobeniusOrbits (HostHyp HGrp hcl)
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution : HostLocal := by
  intro e q d _ _ h
  exact ⟨fun p hp hpp => host_unram h p hp hpp, ⟨host_inertia_two h, host_frob_two h⟩,
    ⟨host_inertia_q h, host_frob_q h⟩, ⟨host_inertia_d h, host_frob_d h⟩⟩
end Formalism.LFunctionChainParameters.LHost
