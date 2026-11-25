-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.host_inertia_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:47:54.752942+00:00
-- url     : https://prove2.me/submissions/78123125-9007-42b0-a6cb-8b8cf954bc08

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_recMap_apply
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_crt
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_exists_hcl
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_mem_host_inertia_iff

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
theorem _root_.solution (h : HostHyp q d) (x : E0 × HA e) : x ∈ (hostData e q d).inertia 2 ↔ x.1 = 0 := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  have hM := (extension_local_parts e q d h).1.2
  rw [mem_host_inertia_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_localUnits_iff, hM] at hu
    rw [recMap_apply, (unitsMap_eq_one_iff _ u).2 (hu.of_dvd (dvd_mul_left d q)),
      (unitsMap_eq_one_iff _ u).2 (hu.of_dvd (dvd_mul_right q d)), sQ_one, sQ_one]
    rfl
  · intro hx
    obtain ⟨x2, hx2⟩ := exists_hcl e x.2
    obtain ⟨u, h1, h2, h3⟩ := host_crt e h x2 1 1
    refine ⟨u, ?_, ?_⟩
    · rw [mem_localUnits_iff, hM]
      exact (Nat.modEq_and_modEq_iff_modEq_mul ((Nat.coprime_primes h.1 h.2.1).2 (HostHyp_ne h).2.2)).1
        ⟨(unitsMap_eq_one_iff _ u).1 h2, (unitsMap_eq_one_iff _ u).1 h3⟩
    · rw [recMap_apply, h1, h2, h3, sQ_one, sQ_one, hx2]
      exact Prod.ext hx.symm rfl
end Formalism.LFunctionChainParameters.LHost
