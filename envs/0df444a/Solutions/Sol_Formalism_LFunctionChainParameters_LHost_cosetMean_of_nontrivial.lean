-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.cosetMean_of_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:27:16.624037+00:00
-- url     : https://prove2.me/submissions/99b8fcd6-a388-4762-9fd8-958b3c0da1d9

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key


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
    (hI : ¬ ∀ x ∈ I, ψ x = 1) : cosetMean I h ψ = 0 := by
  classical
  unfold cosetMean
  push Not at hI
  obtain ⟨y, hy, hy1⟩ := hI
  have key : ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x) = 0 := by
    have h1 : ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x)
        = ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + (y + x)) := by
      symm
      apply Finset.sum_bij (fun x _ => y + x)
      · intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact I.add_mem hy hx
      · intro a _ b _ hab
        exact add_left_cancel hab
      · intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb
        exact ⟨-y + b, by simpa using I.add_mem (I.neg_mem hy) hb, by simp⟩
      · intro x _
        rfl
    have h2 : ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + (y + x))
        = ψ y * ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
      ring
    rw [h2] at h1
    have h3 : (1 - ψ y) * ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x) = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4).symm hy1
    · exact h4
  rw [key, zero_div]
end Formalism.LFunctionChainParameters.LHost
