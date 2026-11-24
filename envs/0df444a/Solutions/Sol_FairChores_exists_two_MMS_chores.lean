-- Prove2me | solution 1 for FairChores.exists_two_MMS_chores
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:54:22.729211+00:00
-- url     : https://prove2.me/submissions/1d8be0bb-1ea7-4782-a5d0-a2b74183cd1b

import Mathlib
import Definitions.Def_RequestProject_ChoresBagFilling
import Definitions.Def_RequestProject_ChoresMMSApprox
import Theorems.Thm_FairChores_cbar_eq_zero_of_MMS_eq_zero
import Theorems.Thm_FairChores_MMS_nonneg
import Theorems.Thm_FairChores_bagfill_exists
import Theorems.Thm_FairChores_cbarSum_empty
import Theorems.Thm_FairChores_exists_outcome_of_preAlloc
import Theorems.Thm_FairChores_wtSum_univ_le_nsmul_MMS
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
namespace FairChores
theorem _root_.solution (hn : 0 < n) (c : Fin n → T → ℝ) (p : T → ℝ)
    (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t) :
    ∃ o : Outcome T n, o.Valid p ∧ ∀ i, cost (c i) o i ≤ 2 * MMS n (c i) p := by
  classical
  set mu : Fin n → ℝ := fun i => MMS n (c i) p with hmudef
  have hmunn : ∀ i, 0 ≤ mu i := fun i => MMS_nonneg (hc i) hn
  -- it suffices to produce a self-service allocation of all chores with costs `≤ 2 · muᵢ`
  suffices hsuff : ∃ P : PreAlloc T n,
      (∀ i j, i ≠ j → Disjoint (P.bundle i) (P.bundle j)) ∧
      (∀ i, Disjoint P.outs (P.bundle i)) ∧
      (P.outs ∪ Finset.univ.biUnion P.bundle = Finset.univ) ∧
      (∀ i, 0 ≤ P.share i) ∧
      (∑ i, P.share i = ∑ t ∈ P.outs, p t) ∧
      (∀ i, cbarSum (c i) p (P.bundle i) + P.share i ≤ 2 * mu i) by
    obtain ⟨P, h1, h2, h3, h4, h5, h6⟩ := hsuff
    obtain ⟨o, hvalid, hcost⟩ := exists_outcome_of_preAlloc P p c hp h1 h2 h3 h4 h5
    exact ⟨o, hvalid, fun i => by rw [hcost i]; exact h6 i⟩
  by_cases hzero : ∃ i0, mu i0 = 0
  · -- some agent can do everything for free; give it all the chores
    obtain ⟨i0, hi0⟩ := hzero
    have hcb : ∀ t, cbar (c i0) p t = 0 := fun t =>
      cbar_eq_zero_of_MMS_eq_zero (hc i0) hp hn hi0 t
    refine ⟨⟨fun j => if j = i0 then Finset.univ else ∅, ∅, fun _ => 0⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      dsimp only
      by_cases hi : i = i0 <;> by_cases hj : j = i0 <;> simp [hi, hj]
      exact absurd (hi.trans hj.symm) hij
    · intro i; simp
    · dsimp only
      simp only [Finset.empty_union]
      refine Finset.eq_univ_iff_forall.mpr fun s => ?_
      exact Finset.mem_biUnion.mpr ⟨i0, Finset.mem_univ _, by simp⟩
    · intro i; exact le_rfl
    · simp
    · intro i
      dsimp only
      by_cases hi : i = i0
      · subst hi
        have hz : cbarSum (c i) p Finset.univ = 0 := by
          simp [cbarSum, hcb]
        simp only [if_true, add_zero, hz, hi0]
        norm_num
      · simp only [if_neg hi, cbarSum_empty, add_zero]
        linarith [hmunn i]
  · -- all thresholds are positive: run the bag-filling algorithm
    push_neg at hzero
    have hmupos : ∀ i, 0 < mu i := fun i => lt_of_le_of_ne (hmunn i) (Ne.symm (hzero i))
    have hAne : (Finset.univ : Finset (Fin n)).Nonempty := by
      rw [← Finset.card_pos, Finset.card_univ, Fintype.card_fin]
      exact hn
    have hinv : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Inv c p mu i (Finset.univ : Finset (Fin n)).card Finset.univ := by
      intro i _
      left
      rw [Finset.card_univ, Fintype.card_fin]
      exact wtSum_univ_le_nsmul_MMS (hc i) hn
    obtain ⟨P, hP, hcost⟩ :=
      bagfill_exists hc hp hmupos (Finset.univ : Finset (Fin n)).card Finset.univ Finset.univ
        rfl hAne hinv
    exact ⟨P, hP.2.2.2.1, hP.2.2.2.2.1, hP.2.2.2.2.2.1, hP.2.2.1, hP.2.2.2.2.2.2,
      fun i => hcost i (Finset.mem_univ i)⟩
end FairChores
