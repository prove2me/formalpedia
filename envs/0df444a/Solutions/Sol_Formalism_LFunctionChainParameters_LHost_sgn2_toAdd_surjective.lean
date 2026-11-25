-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.sgn2_toAdd_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:57:27.727661+00:00
-- url     : https://prove2.me/submissions/0f103b76-91ab-461c-9117-3dc21e02ebac

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
theorem _root_.solution : ∀ x : ZMod 2, ∃ s : ℤˣ, Multiplicative.toAdd (sgn2 s) = x := by decide
end Formalism.LFunctionChainParameters.LHost
