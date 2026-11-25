-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.block_is_run
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:21:09.421959+00:00
-- url     : https://prove2.me/submissions/3fb72452-4f21-47fb-92c1-1b005eb4b90d

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_run_jumps_holds
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
theorem _root_.solution : BlockIsRun := by
  intro n p t a c w ha hpt hn hrun hblock
  have ht : 1 ≤ t := by omega
  have hs : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → (i : ℤ) - a i < (j : ℤ) - a j := by
    intro i j hij
    have h1 : a j ≤ a i := ha (by rw [Fin.le_def]; omega)
    omega
  obtain ⟨j0, hj0⟩ := hblock 0 (by omega)
  have hind : ∀ k : ℕ, k < t → ∃ j : Fin n, (j : ℕ) = (j0 : ℕ) + k ∧ (j : ℤ) - a j = w + k := by
    intro k
    induction k with
    | zero => intro _; exact ⟨j0, by simp, hj0⟩
    | succ k ih =>
      intro hk
      obtain ⟨j, hj, hjw⟩ := ih (by omega)
      obtain ⟨j', hj'⟩ := hblock (k + 1) hk
      push_cast at hj'
      have h1 : (j : ℕ) < (j' : ℕ) := by
        by_contra hcon
        rcases Nat.lt_or_ge (j' : ℕ) (j : ℕ) with h | h
        · have := hs j' j h; omega
        · have : j' = j := Fin.ext (by omega)
          rw [this] at hj'; omega
      have h2 : (j' : ℕ) = (j : ℕ) + 1 := by
        by_contra hcon
        have hlt : (j : ℕ) + 1 < (j' : ℕ) := by omega
        have hb : (j : ℕ) + 1 < n := by have := j'.2; omega
        have e1 := hs j ⟨(j : ℕ) + 1, hb⟩ (by simp)
        have e2 := hs ⟨(j : ℕ) + 1, hb⟩ j' (by simpa using hlt)
        omega
      refine ⟨j', by omega, ?_⟩
      push_cast; omega
  have hval : ∀ k : ℕ, k < t → ∃ j : Fin n, (j : ℕ) = (j0 : ℕ) + k ∧ a j = (j0 : ℤ) - w := by
    intro k hk
    obtain ⟨j, hj, hjw⟩ := hind k hk
    refine ⟨j, hj, ?_⟩
    have : (j : ℤ) = (j0 : ℤ) + k := by exact_mod_cast hj
    omega
  obtain ⟨jl, hjl, hal⟩ := hval (t - 1) (by omega)
  have hjln := jl.2
  have ha0 : a j0 = (j0 : ℤ) - w := by
    obtain ⟨j, hj, h⟩ := hval 0 (by omega)
    have : j = j0 := Fin.ext (by omega)
    rw [← this]; rw [this] at h ⊢; exact h
  have hc : (j0 : ℤ) - w = c := by
    rcases Nat.lt_or_ge p (j0 : ℕ) with h | h
    · have := (hrun j0).2 ⟨by omega, by omega⟩
      omega
    · obtain ⟨j, hj, hv⟩ := hval (p - j0) (by omega)
      have := (hrun j).2 ⟨by omega, by omega⟩
      omega
  have r0 := (hrun j0).1 (by omega)
  have rl := (hrun jl).1 (by omega)
  have hj0p : (j0 : ℕ) = p := by omega
  have hw : w = (p : ℤ) - c := by
    have : (j0 : ℤ) = (p : ℤ) := by exact_mod_cast hj0p
    omega
  refine ⟨hw, ?_⟩
  rw [hw]
  exact (run_jumps_holds n p t a c ha ht hpt hrun).1
end Formalism.IrreducibleCountingLemmas.Z
