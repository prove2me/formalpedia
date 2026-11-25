-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.recMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:27:05.056905+00:00
-- url     : https://prove2.me/submissions/14589e54-4e2f-4919-8a07-728d70f2d527

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation

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
theorem _root_.solution (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (u : (ZMod (hostN e q d))ˣ) :
    Multiplicative.toAdd (recMap e q d u)
      = ((sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u), sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)),
        Additive.ofMul (hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) := rfl
end Formalism.LFunctionChainParameters.LHost
