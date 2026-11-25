-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.frobUnit_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:54:39.135275+00:00
-- url     : https://prove2.me/submissions/89ca5f2e-b17b-4195-9cd9-50f06d81eb02

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_isFrobUnit_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_frobenius_unit_spec

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
theorem _root_.solution {N p : ℕ} [NeZero N] (hp : p.Prime) :
    ((frobUnit N p : (ZMod N)ˣ) : ZMod N).val ≡ p [MOD ordCompl[p] N] ∧
      ((frobUnit N p : (ZMod N)ˣ) : ZMod N).val ≡ 1 [MOD ordProj[p] N] :=
  (isFrobUnit_iff p _).1 (frobenius_unit_spec N p (NeZero.ne N) hp).1
end Formalism.LFunctionChainParameters.LHost
