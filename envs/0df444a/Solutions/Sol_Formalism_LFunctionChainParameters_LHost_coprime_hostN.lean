-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.coprime_hostN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:27:15.454345+00:00
-- url     : https://prove2.me/submissions/80c727ea-652a-4b42-b632-68eb305e9ad8

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
theorem _root_.solution (e : ℕ) {q d p : ℕ} (h : HostHyp q d) (hp : p.Prime) (h2 : p ≠ 2) (hq : p ≠ q) (hd : p ≠ d) :
    p.Coprime (hostN e q d) := by
  unfold hostN
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 h2))
    ((Nat.coprime_primes hp h.1).2 hq)) ((Nat.coprime_primes hp h.2.1).2 hd)
end Formalism.LFunctionChainParameters.LHost
