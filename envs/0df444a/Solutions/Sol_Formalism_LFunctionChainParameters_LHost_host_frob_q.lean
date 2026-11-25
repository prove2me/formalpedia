-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.host_frob_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:12:12.310259+00:00
-- url     : https://prove2.me/submissions/e0651410-fd74-4789-b56e-babd947f8dea

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_jac_q_d
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_recMap_of_modEq

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
theorem _root_.solution (h : HostHyp q d) (hq : q.Coprime (2 ^ (e + 2))) :
    (hostData e q d).frob q = ((0, 0), Additive.ofMul (hcl e (ZMod.unitOfCoprime q hq))) := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  obtain ⟨hP, hM⟩ := (extension_local_parts e q d h).2.1
  obtain ⟨w1, w2⟩ := frobUnit_modEq (N := hostN e q d) h.1
  rw [hM] at w1
  rw [hP] at w2
  change Multiplicative.toAdd (recMap e q d (frobUnit (hostN e q d) q)) = _
  rw [recMap_of_modEq _ q 1 q hq (w1.of_dvd (dvd_mul_left d _)) w2 (w1.of_dvd (dvd_mul_right _ d)),
    jac_q_d h, Nat.cast_one, jacobiSym.one_left]
  rfl
end Formalism.LFunctionChainParameters.LHost
