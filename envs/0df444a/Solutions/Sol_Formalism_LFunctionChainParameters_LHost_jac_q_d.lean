-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.jac_q_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:35:07.917336+00:00
-- url     : https://prove2.me/submissions/025f2b38-e856-40c4-b074-0ff68c23f9b6

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_FrobeniusOrbits_hostRecip


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
theorem _root_.solution {q d : ℕ} (h : HostHyp q d) : jacobiSym (q : ℤ) d = 1 := by
  have h4 : d % 4 = 3 := by have := h.2.2.2.1; omega
  have hodd : Odd d := Nat.odd_iff.2 (by omega)
  have h1 := FrobeniusOrbits.hostRecip q d h
  rw [jacobiSym.neg _ hodd, ZMod.χ₄_nat_three_mod_four h4] at h1
  linarith
end Formalism.LFunctionChainParameters.LHost
