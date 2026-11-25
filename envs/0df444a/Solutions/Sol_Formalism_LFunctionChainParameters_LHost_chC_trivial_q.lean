-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.chC_trivial_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:28.334867+00:00
-- url     : https://prove2.me/submissions/270b15f8-abe0-49f9-8928-f7adb010e8bf

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_inertia_q
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_chC_val

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
theorem _root_.solution (h : HostHyp q d) : ∀ x ∈ (hostData e q d).inertia q, (chC : AddChar (E0 × HA e) ℂ) x = 1 := by
  intro x hx
  rw [chC_val]
  rcases (host_inertia_q h x).1 hx with rfl | rfl <;> simp [sg]
end Formalism.LFunctionChainParameters.LHost
