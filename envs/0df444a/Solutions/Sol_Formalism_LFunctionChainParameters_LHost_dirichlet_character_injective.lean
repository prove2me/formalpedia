-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.dirichlet_character_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:46:17.173709+00:00
-- url     : https://prove2.me/submissions/b5bc28f4-ef7f-4f79-a459-c119f267598d

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_dirChar_unit
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_recSurjective_valid

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
theorem _root_.solution : DirCharInjective := by
  intro e q d _ _ h ψ ψ' hψ
  apply DFunLike.ext
  intro x
  obtain ⟨u, hu⟩ := recSurjective_valid e q d h (Multiplicative.ofAdd x)
  have h1 := dirChar_unit (recMap e q d) ψ u
  have h2 := dirChar_unit (recMap e q d) ψ' u
  rw [hu] at h1 h2
  have h3 : dirChar (recMap e q d) ψ (u : ZMod (hostN e q d)) = dirChar (recMap e q d) ψ' (u : ZMod (hostN e q d)) := by
    rw [hψ]
  rw [h1, h2] at h3
  exact h3
end Formalism.LFunctionChainParameters.LHost
