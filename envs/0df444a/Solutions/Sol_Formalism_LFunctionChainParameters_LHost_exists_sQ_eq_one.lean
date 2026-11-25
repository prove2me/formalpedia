-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.exists_sQ_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:38:50.082041+00:00
-- url     : https://prove2.me/submissions/7233b5bc-a3e0-4e1d-a51f-0152d4538a2e

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_sgn2_toAdd_eq_ite

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
theorem _root_.solution (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) : ∃ x : (ZMod l)ˣ, sQ l x = 1 := by
  obtain ⟨x, hx⟩ := quadraticChar_exists_neg_one' (F := ZMod l) (by rwa [ZMod.ringChar_zmod_n])
  refine ⟨x, ?_⟩
  unfold sQ
  rw [sgn2_toAdd_eq_ite, MulChar.coe_toUnitHom, hx]
  simp
end Formalism.LFunctionChainParameters.LHost
