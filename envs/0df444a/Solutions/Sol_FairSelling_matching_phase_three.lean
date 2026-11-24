-- Prove2me | solution 1 for FairSelling.matching_phase_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:06:41.36324+00:00
-- url     : https://prove2.me/submissions/b0ed9c23-3ea8-40b0-bc6b-243c01133e5b

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_matching_phase_two
import Theorems.Thm_FairSelling_outcome_of_assignment
import Theorems.Thm_FairSelling_fin3_others
import Theorems.Thm_FairSelling_special_case_pure_allocation
import Theorems.Thm_FairSelling_singleLoss_of_canonical_bundle
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_fin3_cover
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (a : Fin 3) (hmax : ∀ i, MMS 3 (v i) p ≤ MMS 3 (v a) p)
    (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (lo : Fin 3)
    (hcan : IsCanonicalStrict (v a) p ((3 / 4 : ℝ) * MMS 3 (v a) p) kept sold money lo) :
    (∃ o : Outcome G 3, o.Valid p ∧
        ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i)
      ∨ SingleLossConfig v p := by
  classical
  have hcanon := hcan.1
  have hcard := hcan.2.1
  obtain ⟨hdisj, hsold, hm0, hmsum, hacc, -⟩ := id hcanon
  obtain ⟨k1, k2, hk1, hk2, hk12⟩ := fin3_others lo
  obtain ⟨b, d, hba, hda, hbd⟩ := fin3_others a
  -- the two non-leftovers bundles and the two non-partitioning agents, indexed by `Fin 2`
  set bd : Fin 2 → Fin 3 := ![b, d] with hbdf
  set kk : Fin 2 → Fin 3 := ![k1, k2] with hkkf
  have hbd0 : bd 0 = b := rfl
  have hbd1 : bd 1 = d := rfl
  have hkk0 : kk 0 = k1 := rfl
  have hkk1 : kk 1 = k2 := rfl
  have hbdinj : ∀ i j : Fin 2, i ≠ j → bd i ≠ bd j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm hbd]
  have hkkinj : ∀ i j : Fin 2, i ≠ j → kk i ≠ kk j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm hk12]
  have hkklo : ∀ i : Fin 2, kk i ≠ lo := by
    intro i; fin_cases i <;> simpa [hkkf] using ‹_›
  have hbda : ∀ i : Fin 2, bd i ≠ a := by
    intro i; fin_cases i <;> simpa [hbdf] using ‹_›
  set acc : Fin 2 → Fin 2 → Bool := fun j k =>
    decide ((3 / 4 : ℝ) * MMS 3 (v (bd j)) p ≤
      vbarSum (v (bd j)) p (kept (kk k)) + money (kk k)) with haccdef
  have hacc_true : ∀ j k, acc j k = true → (3 / 4 : ℝ) * MMS 3 (v (bd j)) p ≤
      vbarSum (v (bd j)) p (kept (kk k)) + money (kk k) := by
    intro j k h; simpa [haccdef] using of_decide_eq_true h
  have hacc_false : ∀ j k, acc j k = false →
      vbarSum (v (bd j)) p (kept (kk k)) + money (kk k) ≤
        (3 / 4 : ℝ) * MMS 3 (v (bd j)) p := by
    intro j k h
    simp only [haccdef, decide_eq_false_iff_not, not_le] at h
    exact h.le
  rcases matching_phase_two acc with ⟨σ, hσ⟩ | ⟨k, hk⟩ | ⟨j, j', hjj', hall, hnone⟩
  · -- Perfect matching: the partitioning agent takes the leftovers bundle.
    refine Or.inl ?_
    have hne : σ 0 ≠ σ 1 := fun h => by simpa using σ.injective h
    refine outcome_of_assignment v p hp hcanon a b d hba.symm hda.symm hbd
      lo (kk (σ 0)) (kk (σ 1)) (Ne.symm (hkklo _)) (Ne.symm (hkklo _)) (hkkinj _ _ hne)
      (hacc lo) ?_ ?_
    · simpa [hbd0] using hacc_true 0 (σ 0) (hσ 0)
    · simpa [hbd1] using hacc_true 1 (σ 1) (hσ 1)
  · -- A non-leftovers bundle rejected by both non-partitioning agents: hand it to the
    -- partitioning agent.
    refine Or.inr (singleLoss_of_canonical_bundle v p hp a (hv a) hmax hcan (kk k) (hkklo k) a
      (hacc (kk k)) (fun i hi => Or.inr ?_))
    rcases fin3_cover hba.symm hda.symm hbd i with h | h | h
    · exact absurd h hi
    · rw [h]; simpa [hbd0] using hacc_false 0 k (hk 0)
    · rw [h]; simpa [hbd1] using hacc_false 1 k (hk 1)
  · -- The special case: agent `bd j` accepts both bundles, agent `bd j'` accepts neither.
    set B : Fin 3 := bd j with hB
    set D : Fin 3 := bd j' with hD
    have hBD : B ≠ D := hbdinj j j' hjj'
    have hBa : B ≠ a := hbda j
    have hDa : D ≠ a := hbda j'
    have hBacc : ∀ i : Fin 2, (3 / 4 : ℝ) * MMS 3 (v B) p ≤
        vbarSum (v B) p (kept (kk i)) + money (kk i) := fun i => hacc_true j i (hall i)
    have hDrej : ∀ i : Fin 2, vbarSum (v D) p (kept (kk i)) + money (kk i) ≤
        (3 / 4 : ℝ) * MMS 3 (v D) p := fun i => hacc_false j' i (hnone i)
    by_cases hDlo : (3 / 4 : ℝ) * MMS 3 (v D) p ≤ vbarSum (v D) p (kept lo) + money lo
    · -- `D` accepts the leftovers bundle: everybody is matched after all.
      refine Or.inl (outcome_of_assignment v p hp hcanon a B D (Ne.symm hBa) (Ne.symm hDa) hBD
        (kk 0) (kk 1) lo (hkkinj 0 1 (by decide)) (hkklo 0) (hkklo 1)
        (hacc (kk 0)) (hBacc 1) hDlo)
    · -- `D` rejects every bundle.
      push_neg at hDlo
      have hDall : ∀ k : Fin 3, vbarSum (v D) p (kept k) + money k ≤
          (3 / 4 : ℝ) * MMS 3 (v D) p := by
        intro k
        rcases fin3_cover hk12 hk1 hk2 k with h | h | h
        · rw [h]; simpa [hkk0] using hDrej 0
        · rw [h]; simpa [hkk1] using hDrej 1
        · rw [h]; exact hDlo.le
      by_cases hpure : money k1 = 0 ∨ money k2 = 0
      · -- One of the two bundles is pure: a complete allocation exists outright.
        refine Or.inl ?_
        rcases hpure with h0 | h0
        · exact special_case_pure_allocation v p hv hp a B D (Ne.symm hBa) (Ne.symm hDa) hBD
            hnobig kept sold money lo hcanon hcard k1 k2 hk1 hk2 hk12 h0
            (by simpa [hkk0] using hBacc 0) hDall
        · exact special_case_pure_allocation v p hv hp a B D (Ne.symm hBa) (Ne.symm hDa) hBD
            hnobig kept sold money lo hcanon hcard k2 k1 hk2 hk1 (Ne.symm hk12) h0
            (by simpa [hkk1] using hBacc 1) hDall
      · -- Both bundles are singleton bundles: hand one of them to `B`, a single loss event.
        refine Or.inr (singleLoss_of_canonical_bundle v p hp a (hv a) hmax hcan k1 hk1 B
          (by simpa [hkk0] using hBacc 0) (fun i hi => ?_))
        rcases fin3_cover hBa hBD (Ne.symm hDa) i with h | h | h
        · exact absurd h hi
        · exact Or.inl h
        · exact Or.inr (by rw [h]; exact hDall k1)
end FairSelling
