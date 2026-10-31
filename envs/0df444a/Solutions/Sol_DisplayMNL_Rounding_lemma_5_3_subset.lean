-- Prove2me | solution 1 for DisplayMNL.Rounding.lemma_5_3_subset
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:35:59.596235+00:00
-- url     : https://prove2.me/submissions/a4f946ec-7517-49fd-b60d-7eb1e1378d93

import Mathlib
import Definitions.Def_DisplayMNL_Rounding_Model

open Finset

open DisplayMNL.Rounding in
theorem solution {n : ℕ} (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) (A : Fin n ≃ Fin n)
    (hst : Standing I ε) (hk1 : 1 ≤ kmid) (hk2 : kmid + 1 ≤ n)
    (hF : IsFeasible I ε kmid s) (hR : IsRounded I s kmid A)
    (j : ℕ) (hj1 : 1 ≤ j) (hjT : j ≤ s.T) :
    pre A (etil s kmid j) ⊆ s.sp j := by
  obtain ⟨hT1, _, _, ⟨_, hSmT, hSpT⟩, htr⟩ := hF
  rw [(hR j hj1 hjT).1]
  -- S⁻_i ⊆ S⁺_i for i ∈ [1, T]
  have hsmsp : ∀ i, 1 ≤ i → i ≤ s.T → s.sm i ⊆ s.sp i := by
    intro i hi1 hiT
    rcases Nat.lt_or_ge i s.T with h | h
    · have := (htr (i + 1) (by omega) (by omega)).1.1
      rw [Nat.add_sub_cancel] at this
      exact this
    · have hi : i = s.T := le_antisymm hiT h
      have hi0 : i ≠ 0 := by omega
      rw [hi]
      unfold DPSeq.sm DPSeq.sp
      rw [if_neg (by omega), min_self, hSmT, hSpT]
  have key : ∀ i, 1 ≤ i → i ≤ s.T → U s kmid i ⊆ s.sp i := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro _ hiT
      show U s kmid i ∪ deltaStep s kmid (i + 1) (U s kmid i) ⊆ s.sp (i + 1)
      apply Finset.union_subset
      · rcases Nat.eq_zero_or_pos i with h0 | hpos
        · subst h0; simp [U]
        · have h1 := ih hpos (by omega)
          have h2 := (htr (i + 1) (by omega) hiT).1.2
          rw [Nat.add_sub_cancel] at h2
          exact h1.trans h2
      · unfold deltaStep
        split_ifs
        · exact Finset.sdiff_subset.trans (hsmsp (i + 1) (by omega) hiT)
        · exact Finset.sdiff_subset
  exact key j hj1 hjT
