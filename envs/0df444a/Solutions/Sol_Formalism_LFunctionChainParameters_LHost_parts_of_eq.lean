-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.parts_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:27:24.604271+00:00
-- url     : https://prove2.me/submissions/7874b66b-9c58-433d-a91f-6e61e606ea19

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
theorem _root_.solution {N p k m : ℕ} (hp : p.Prime) (hN : N = p ^ k * m) (hm : ¬ p ∣ m) (hm0 : m ≠ 0) :
    ordProj[p] N = p ^ k ∧ ordCompl[p] N = m := by
  subst hN
  have h2 := Nat.ordCompl_pow_mul_of_not_dvd k hp hm
  have h1 := Nat.ordProj_mul_ordCompl_eq_self (p ^ k * m) p
  rw [h2] at h1
  exact ⟨Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hm0) h1, h2⟩
end Formalism.LFunctionChainParameters.LHost
