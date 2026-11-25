-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.jac_flip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:35:46.588036+00:00
-- url     : https://prove2.me/submissions/84d1a994-cfed-4c38-a69c-c4b43a057726

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
theorem _root_.solution {l m : ℕ} (hl : l % 4 = 3) (hm : Odd m) : jacobiSym (m : ℤ) l = jacobiSym (-(l : ℤ)) m := by
  rw [jacobiSym.neg _ hm]
  have hl' : Odd l := Nat.odd_iff.2 (by omega)
  rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hm) with h1 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h1, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h1 hl']
  · rw [ZMod.χ₄_nat_three_mod_four h3, jacobiSym.quadratic_reciprocity_three_mod_four h3 hl]
    ring
end Formalism.LFunctionChainParameters.LHost
