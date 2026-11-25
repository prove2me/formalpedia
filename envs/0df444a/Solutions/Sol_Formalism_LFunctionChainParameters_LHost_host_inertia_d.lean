-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.host_inertia_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:48:31.355432+00:00
-- url     : https://prove2.me/submissions/c845c3b4-25d9-40b6-ba9e-f6b4d14769c4

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_unitsMap_eq_one_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_mem_localUnits_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_hostN_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_HostHyp_ne
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_extension_local_parts
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_sQ_one
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_exists_sQ_eq_one
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_zmod_two_eq_zero_or_eq_one
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_recMap_apply
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_crt
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_mem_host_inertia_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_hcl_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_hcl_one


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
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution (h : HostHyp q d) (x : E0 × HA e) : x ∈ (hostData e q d).inertia d ↔ x = 0 ∨ x = sgc0 := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  have hM := (extension_local_parts e q d h).2.2.2
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have c2q : (2 ^ (e + 2)).Coprime q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two h.1).2 hq2.symm)
  rw [mem_host_inertia_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_localUnits_iff, hM] at hu
    rw [recMap_apply, (unitsMap_eq_one_iff _ u).2 (hu.of_dvd (dvd_mul_left q _)),
      (unitsMap_eq_one_iff (two_dvd_hostN e q d) u).2 (hu.of_dvd (dvd_mul_right _ q)), sQ_one, hcl_one]
    rcases zmod_two_eq_zero_or_eq_one (sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u)) with h0 | h0 <;> rw [h0]
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl⟩
    · obtain ⟨xd, hxd⟩ := exists_sQ_eq_one d hd2
      obtain ⟨u, h1, h2, h3⟩ := host_crt e h 1 1 xd
      refine ⟨u, ?_, ?_⟩
      · rw [mem_localUnits_iff, hM]
        exact (Nat.modEq_and_modEq_iff_modEq_mul c2q).1
          ⟨(unitsMap_eq_one_iff _ u).1 h1, (unitsMap_eq_one_iff _ u).1 h2⟩
      · rw [recMap_apply, h1, h2, h3, sQ_one, hxd, hcl_one]
        rfl
end Formalism.LFunctionChainParameters.LHost
