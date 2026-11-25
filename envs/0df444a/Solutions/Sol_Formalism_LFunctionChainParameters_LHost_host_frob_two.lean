-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.host_frob_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:12:25.849283+00:00
-- url     : https://prove2.me/submissions/d841688b-c9a6-4dfd-9cc4-9337d7d54687

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_frobUnit_modEq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_hostN_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_extension_local_parts
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_jac_two_d
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_jac_two_q
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_recMap_of_modEq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_hcl_one
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_unitOfCoprime_one
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
theorem _root_.solution (h : HostHyp q d) : (hostData e q d).frob 2 = sg := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  obtain ⟨hP, hM⟩ := (extension_local_parts e q d h).1
  obtain ⟨w1, w2⟩ := frobUnit_modEq (N := hostN e q d) Nat.prime_two
  rw [hM] at w1
  rw [hP] at w2
  change Multiplicative.toAdd (recMap e q d (frobUnit (hostN e q d) 2)) = _
  rw [recMap_of_modEq _ 2 2 1 (Nat.coprime_one_left _) (w1.of_dvd (dvd_mul_left d q)) (w1.of_dvd (dvd_mul_right q d)) w2,
    jac_two_d h, jac_two_q h, unitOfCoprime_one, hcl_one]
  rfl
end Formalism.LFunctionChainParameters.LHost
