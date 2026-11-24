-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.run_jumps_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:33.461489+00:00
-- url     : https://prove2.me/submissions/b6e8f2d2-5040-40ea-8a6a-226682a136b9

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_natAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : RunJumps := by
  intro n p t a c ha ht hpt hrun
  have hp : p < n := by omega
  have hc : a ⟨p, hp⟩ = c := (hrun ⟨p, hp⟩).2 ⟨le_refl _, by simp; omega⟩
  have hlow : ∀ j : Fin n, (j : ℕ) < p → c + 1 ≤ a j := by
    intro j hj
    have h1 : a ⟨p, hp⟩ ≤ a j := ha (by rw [Fin.le_def]; simp; omega)
    have h2 : a j ≠ c := fun h => by have := (hrun j).1 h; omega
    omega
  have hhigh : ∀ j : Fin n, p + t ≤ (j : ℕ) → a j ≤ c - 1 := by
    intro j hj
    have h1 : a j ≤ a ⟨p, hp⟩ := ha (by rw [Fin.le_def]; simp; omega)
    have h2 : a j ≠ c := fun h => by have := (hrun j).1 h; omega
    omega
  have hmid : ∀ j : Fin n, p ≤ (j : ℕ) → (j : ℕ) < p + t → a j = c := fun j h1 h2 =>
    (hrun j).2 ⟨h1, h2⟩
  refine ⟨fun j => ?_, fun k hk => ?_, fun j => ?_⟩
  · rcases lt_or_ge (j : ℕ) p with h | h
    · have := hlow j h
      constructor
      · rintro ⟨h1, h2⟩; omega
      · rintro ⟨h1, h2⟩; omega
    · rcases lt_or_ge (j : ℕ) (p + t) with h' | h'
      · have := hmid j h h'
        constructor
        · intro _; exact ⟨h, h'⟩
        · intro _; constructor <;> omega
      · have := hhigh j h'
        constructor
        · rintro ⟨h1, h2⟩; omega
        · rintro ⟨h1, h2⟩; omega
  · refine ⟨⟨p + k, by omega⟩, ?_⟩
    have := hmid ⟨p + k, by omega⟩ (by simp) (by simp; omega)
    rw [this]; push_cast; ring
  · rcases lt_or_ge (j : ℕ) p with h | h
    · have := hlow j h
      constructor <;> omega
    · rcases lt_or_ge (j : ℕ) (p + t) with h' | h'
      · have := hmid j h h'
        constructor <;> omega
      · have := hhigh j h'
        constructor <;> omega
end Formalism.IrreducibleCountingLemmas.Z
