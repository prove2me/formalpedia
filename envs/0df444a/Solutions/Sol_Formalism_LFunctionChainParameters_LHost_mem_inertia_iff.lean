-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.mem_inertia_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:27:20.557833+00:00
-- url     : https://prove2.me/submissions/e59e05e1-cc8f-4660-aa15-6c372ef82b64

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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution {N : ℕ} (q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (p : ℕ) (x : E0 × H) :
    x ∈ (cftData q1 d r).inertia p ↔ ∃ u ∈ localUnits N p, Multiplicative.toAdd (r u) = x := by
  change Multiplicative.ofAdd x ∈ (localUnits N p).map r ↔ _
  rw [Subgroup.mem_map]
  rfl
end Formalism.LFunctionChainParameters.LHost
