-- Prove2me | solution 1 for EnvyFreeCake104.Divide.intervalSearch_certificate__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T01:57:10.587201+00:00
-- url     : https://prove2.me/submissions/920afc61-47da-4ddc-a448-ae8b65079e32

import Definitions.Def_EnvyFreeCake104_Divide_Query
import Mathlib.Tactic.Linarith

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

private theorem search_offset__p2m_518aa50c_865e_406f_a8d5_8825bd8e452f_a1
    {ι : Type} (s : Rec ι) (i : ι) (Q : Piece) :
    ∀ (n : ℕ) (w : ℝ), Q ≠ [] → 0 ≤ w → w ≤ s.pieceVal i Q →
      ∃ (k : ℕ) (r : ℝ),
        findInterval s i Q n w = some (n + k, r) ∧
        k < Q.length ∧ 0 ≤ r ∧ r ≤ s.intervalVal i (Q.getD k default) ∧
        s.pieceVal i (Q.take k) + r = w ∧
        ∀ j : ℕ, j < k → s.pieceVal i (Q.take (j + 1)) < w := by
  induction Q with
  | nil =>
      intro n w hne
      exact (hne rfl).elim
  | cons I R ih =>
      intro n w hne hw hbudget
      have hval (L : Piece) :
          s.pieceVal i (I :: L) = s.intervalVal i I + s.pieceVal i L := by
        simp [Rec.pieceVal]
      by_cases hhit : w ≤ s.intervalVal i I
      · refine ⟨0, w, ?_, ?_, hw, ?_, ?_, ?_⟩
        · simp [findInterval, hhit]
        · simp
        · simpa using hhit
        · simp [Rec.pieceVal]
        · intro j hj
          omega
      · have hv : s.intervalVal i I < w := lt_of_not_ge hhit
        have hres : 0 ≤ w - s.intervalVal i I := by linarith
        have hb : w - s.intervalVal i I ≤ s.pieceVal i R := by
          rw [hval] at hbudget
          linarith
        have hR : R ≠ [] := by
          intro he
          subst R
          simp [Rec.pieceVal] at hb
          linarith
        obtain ⟨k, r, hsearch, hk, hr0, hrle, hbalance, hstrict⟩ :=
          ih (n + 1) (w - s.intervalVal i I) hR hres hb
        refine ⟨k + 1, r, ?_, ?_, hr0, ?_, ?_, ?_⟩
        · simpa [findInterval, hhit, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hsearch
        · simpa only [List.length_cons] using Nat.succ_lt_succ hk
        · simpa only [List.getD_cons_succ] using hrle
        · rw [List.take_succ_cons, hval]
          linarith
        · intro j hj
          cases j with
          | zero =>
              simpa [Rec.pieceVal] using hv
          | succ j =>
              have hjk : j < k := by omega
              have ht := hstrict j hjk
              rw [List.take_succ_cons, hval]
              linarith

theorem solution
    {ι : Type} (s : Rec ι) (i : ι) (Q : Piece) (hne : Q ≠ [])
    (w : ℝ) (hw : 0 ≤ w) (hbudget : w ≤ s.pieceVal i Q) :
    ∃ (k : ℕ) (r : ℝ),
      findInterval s i Q 0 w = some (k, r) ∧
      k < Q.length ∧ 0 ≤ r ∧ r ≤ s.intervalVal i (Q.getD k default) ∧
      s.pieceVal i (Q.take k) + r = w ∧
      ∀ j : ℕ, j < k → s.pieceVal i (Q.take (j + 1)) < w := by
  simpa only [Nat.zero_add] using
    search_offset__p2m_518aa50c_865e_406f_a8d5_8825bd8e452f_a1 s i Q 0 w hne hw hbudget
