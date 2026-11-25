-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.extension_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:33:31.489952+00:00
-- url     : https://prove2.me/submissions/088dc8ed-800a-4341-a3e1-b5242ee47f97

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_HostHyp_ne
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_unram
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_inertia_two
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_inertia_q
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_inertia_d
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_frob_two
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_frob_q
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_coprime_hostN

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
theorem _root_.solution : HostFactsHost := by
  intro e q d _ _ h
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have cq : q.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes h.1 Nat.prime_two).2 hq2)
  refine ⟨h.1, h.2.1, hq2, hd2, hqd, ?_, ?_, ?_, host_inertia_d h⟩
  · intro p hp h2 hq hd
    exact (host_unram h p (coprime_hostN e h hp h2 hq hd) hp).1
  · rintro p (rfl | hp) x hx
    · have := (host_inertia_two h x).1 hx
      change x.1.1 = 0
      rw [this]
      rfl
    · have hp' : p = q := hp
      rw [hp'] at hx
      rcases (host_inertia_q h x).1 hx with rfl | rfl <;> rfl
  · rintro p (rfl | hp)
    · rw [host_frob_two h]
      rfl
    · have hp' : p = q := hp
      rw [hp', host_frob_q h cq]
      rfl
end Formalism.LFunctionChainParameters.LHost
