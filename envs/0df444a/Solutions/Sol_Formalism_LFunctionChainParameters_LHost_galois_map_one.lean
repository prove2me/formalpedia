-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.galois_map_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:58:22.32725+00:00
-- url     : https://prove2.me/submissions/2672a24d-9bc4-49e3-92c3-c44b3a17e596

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
theorem _root_.solution (e : ℕ) : galoisToProduct e 1 = 0 := by
  unfold galoisToProduct
  simp only [Prod.fst_one, Prod.snd_one, map_one]
  rfl
end Formalism.LFunctionChainParameters.LHost
