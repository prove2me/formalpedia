-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.cast_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:52:48.654856+00:00
-- url     : https://prove2.me/submissions/5345fccb-fabb-49a8-b9c7-9229d88c9aec

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_cast_eq_natCast_iff

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
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution {N : ℕ} [NeZero N] (x : ZMod N) (c : ℕ) :
    (x.cast : ZMod c) = 1 ↔ x.val ≡ 1 [MOD c] := by
  rw [← cast_eq_natCast_iff, Nat.cast_one]
end Formalism.LFunctionChainParameters.LHost
