-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.cosetMean_of_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:27:18.027146+00:00
-- url     : https://prove2.me/submissions/ac33f297-c061-4f5f-899a-c3b4a9302bef

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation

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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution (I : AddSubgroup (E0 × H)) (h : E0 × H) (ψ : AddChar (E0 × H) ℂ)
    (hI : ∀ x ∈ I, ψ x = 1) : cosetMean I h ψ = ψ h := by
  classical
  unfold cosetMean
  have h0 : ((univ.filter (fun x => x ∈ I)).card : ℂ) ≠ 0 := by
    have : (0 : E0 × H) ∈ univ.filter (fun x => x ∈ I) := by simp [I.zero_mem]
    exact_mod_cast (Finset.card_pos.2 ⟨_, this⟩).ne'
  rw [div_eq_iff h0, Finset.sum_congr rfl (g := fun _ => ψ h)]
  · rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · intro x hx
    rw [AddChar.map_add_eq_mul, hI x (by simpa using hx), mul_one]
end Formalism.LFunctionChainParameters.LHost
