-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.recSurjective_valid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:12:16.888268+00:00
-- url     : https://prove2.me/submissions/7849aca8-98c1-449c-82c7-325ca9ca5407

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_HostHyp_ne
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_exists_sQ_eq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_recMap_apply
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_crt
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_exists_hcl

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
theorem _root_.solution : RecSurjective := by
  intro e q d _ _ h y
  obtain ⟨hq2, hd2, -⟩ := HostHyp_ne h
  obtain ⟨xd, hxd⟩ := exists_sQ_eq d hd2 (Multiplicative.toAdd y).1.1
  obtain ⟨xq, hxq⟩ := exists_sQ_eq q hq2 (Multiplicative.toAdd y).1.2
  obtain ⟨x2, hx2⟩ := exists_hcl e (Multiplicative.toAdd y).2
  obtain ⟨u, h1, h2, h3⟩ := host_crt e h x2 xq xd
  refine ⟨u, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [recMap_apply, h1, h2, h3, hxd, hxq, hx2]
end Formalism.LFunctionChainParameters.LHost
