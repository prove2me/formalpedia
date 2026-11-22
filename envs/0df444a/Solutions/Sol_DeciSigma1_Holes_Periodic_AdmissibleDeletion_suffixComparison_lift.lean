-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.suffixComparison_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:59:57.487306+00:00
-- url     : https://prove2.me/submissions/ef7b443a-0fd9-443c-988a-998b32ff61ab

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_drop_prefix_iff_suffixComparison
public import Theorems.Thm_DeciSigma1_Holes_Periodic_SuffixComparison_shift
public import Theorems.Thm_DeciSigma1_Holes_Periodic_SuffixComparison_lt_length
public import Theorems.Thm_DeciSigma1_Holes_Periodic_copy_stretch
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_piece_mem
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_room
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_nojun_end
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_end_sub_of_image_eq
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_noJunction_window
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_suffixComparison
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_mod_eq_of_add_mul
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_lift_in_pieces
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_exists_canonicalCut
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_exists_imagePiece
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_followerEdge_cases
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_len
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_mem_iff
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop_eq_length_iff
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_len_eq_retainedLength_add
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_length_editedTuple
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_retainedCount_lt_length
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_runPrefix_canonicalCut
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_runPrefix_imagePiece
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_text_canonicalCut
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_boundaryMargin
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_piecesOf
public import Theorems.Thm_DeciSigma1_Holes_Periodic_two_d_le_boundaryMargin
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
public import Theorems.Thm_P2M_DeciSigma1_Holes_Periodic_AdmissibleDeletion_getElem__imagePiece_5b6104921581
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_coordinate
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_start
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_stop
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


section
@[expose] public section
namespace DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
namespace SuffixComparison
variable {y z : List α} {b a : ℕ}
end SuffixComparison
section Copy
variable [DecidableEq α] {V : Fin k → List α} {d : ℕ}
end Copy
section PieceCmp
variable [DecidableEq α] {W : Fin k → List α} {d : ℕ}
end PieceCmp
namespace AdmissibleDeletion
variable [DecidableEq α] {W : Fin k → List α} {ρ : List α} {N : ℕ} {x : Piece W ρ.length → ℕ}
variable (hx : AdmissibleDeletion W ρ N x)
include hx
private theorem suffixComparison_lift_of_piece {S : Type} [Fintype S] (T : Table α S k)
    (hNS : N = Fintype.card S)
    (hN : 0 < N) (i j : Fin k) {a' b' : ℕ}
    (hb' : b' ≤ (editedTuple W ρ N x j).length)
    (hcmp : SuffixComparison (editedTuple W ρ N x j) b' (editedTuple W ρ N x i) a')
    (hα : ∃ P' : Piece (editedTuple W ρ N x) ρ.length, P'.coordinate = j ∧
      P' ∈ piecesOf (editedTuple W ρ N x) ρ ∧ P'.start ≤ b' ∧ b' + 2 * ρ.length < P'.stop) :
    ∃ a ≤ (W i).length, ∃ b ≤ (W j).length, SuffixComparison (W j) b (W i) a ∧
      T.runPrefix W i a = T.runPrefix (editedTuple W ρ N x) i a' ∧ T.runPrefix W j b =
          T.runPrefix (editedTuple W ρ N x) j b' := by
  classical
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have h2d := Periodic.two_d_le_boundaryMargin hN ρ.length
  have hag : ∀ n < (editedTuple W ρ N x j).length - b',
      (editedTuple W ρ N x j)[b' + n]? = (editedTuple W ρ N x i)[a' + n]? :=
          fun n hn => hcmp n (by omega)
  have hag' : ∀ n < (editedTuple W ρ N x j).length - b',
      (editedTuple W ρ N x i)[a' + n]? = (editedTuple W ρ N x j)[b' + n]? :=
          fun n hn => (hag n hn).symm
  have hKc : Periodic.stateTransientLength N ρ.length + Periodic.statePeriodModulus N ρ.length ≤
      Periodic.comparisonGap N ρ.length := by
    unfold Periodic.comparisonGap Periodic.boundaryMargin; omega
  obtain ⟨P', hP'l, hP'm, hP's, hP'e⟩ := hα
  have hd := P'.period_pos
  have hP'le := P'.stop_le_length; rw [hP'l] at hP'le
  have hP'L := P'.start_add_len
  obtain ⟨P, hP⟩ := hx.exists_imagePiece P'
  have hPl : P.coordinate = j := by rw [← hP'l, ← hP]; rfl
  have hPm : P ∈ piecesOf W ρ := (hx.imagePiece_mem_iff P).mp (hP ▸ hP'm)
  have hnP : retainedLength (N := N) (x := x) P = P'.len := by rw [← hx.imagePiece_len, hP]
  have hPs' : (hx.imagePiece P).start = P'.start := by rw [hP]
  have hLP := hx.len_eq_retainedLength_add P
  obtain ⟨Q', hQ'l, hQ's, hQ'e, hQ'cls, hQ'e'⟩ := copy_stretch hag P' hP'l hP's
    (ℓ := P'.stop - b') (by omega) (by omega) (by omega)
  have hQ'm : Q' ∈ piecesOf (editedTuple W ρ N x) ρ := by
    rw [mem_piecesOf]; exact hQ'cls.trans ((mem_piecesOf _).mp hP'm)
  obtain ⟨Q, hQ⟩ := hx.exists_imagePiece Q'
  have hQl : Q.coordinate = i := by rw [← hQ'l, ← hQ]; rfl
  have hQm : Q ∈ piecesOf W ρ := (hx.imagePiece_mem_iff Q).mp (hQ ▸ hQ'm)
  have hnQ : retainedLength (N := N) (x := x) Q = Q'.len := by rw [← hx.imagePiece_len, hQ]
  have hQs' : (hx.imagePiece Q).start = Q'.start := by rw [hQ]
  have hLQ := hx.len_eq_retainedLength_add Q
  have hQ'L := Q'.start_add_len
  have hQ'le := Q'.stop_le_length; rw [hQ'l] at hQ'le
  have hPsl := P.start_add_len
  have hQsl := Q.start_add_len
  have hPle := P.stop_le_length; rw [hPl] at hPle
  have hQle := Q.stop_le_length; rw [hQl] at hQle
  -- the lift at original offsets `oT`, `oS` with the states and phases of the new offsets
  have lift : ∀ oT oS, oT ≤ P.len → oS ≤ Q.len → SameStatePhase N ρ.length oT (b' - P'.start) →
      SameStatePhase N ρ.length oS (a' - Q'.start) → P.len - oT ≤ Q.len - oS →
      (P.stop = (W j).length ∨
        (P.len - oT = Q.len - oS ∧ SuffixComparison (W j) P.stop (W i) Q.stop)) →
      ∃ a ≤ (W i).length, ∃ b ≤ (W j).length, SuffixComparison (W j) b (W i) a ∧
        T.runPrefix W i a = T.runPrefix (editedTuple W ρ N x) i a' ∧
          T.runPrefix W j b = T.runPrefix (editedTuple W ρ N x) j b' := by
    intro oT oS hoT hoS hT hS hlen hfol
    obtain ⟨hc, hqb, hqa⟩ := hx.lift_in_pieces T hNS hPl hQl (pT := b' - P'.start)
      (pS := a' - Q'.start) (by omega) (by omega) (by omega) (by omega) hoT hoS hT hS hcmp hlen
      hfol
    exact ⟨_, by omega, _, by omega, hc, hqa, hqb⟩
  by_cases hterm : P'.stop = (editedTuple W ρ N x j).length
  · -- the target suffix lies wholly inside its last piece
    have hE : P.stop = (W j).length := by
      rw [← hPl]; exact (hx.imagePiece_stop_eq_length_iff P).mp (by rw [hP, hterm, hPl])
    have hG : FollowerEdge P Q := Or.inl (by
      unfold Piece.follower; rw [hPl, hE, List.drop_length]; exact List.nil_prefix)
    by_cases hA : Periodic.stateTransientLength N ρ.length ≤ b' - P'.start ∨ x P = 0
    · -- end-relative target offset
      refine lift (b' - P'.start + Periodic.statePeriodModulus N ρ.length * x P) _ (by omega)
        (by omega) ?_ (Or.inl rfl) (by omega) (Or.inl hE)
      rcases hA with h | h
      · exact .inr ⟨by omega, h, Nat.add_mul_mod_self_left _ _ _⟩
      · exact .inl (by rw [h]; simp)
    · push Not at hA
      rcases hx.followerEdge_cases hPm hQm hG with hxe | ⟨hf1, hf1'⟩ | ⟨hf2, hf2'⟩
      · exact lift _ _ (by omega) (by omega) (Or.inl rfl) (Or.inl rfl)
          (by rw [hxe] at hLP; omega) (Or.inl hE)
      · by_cases hpS : a' - Q'.start < Periodic.stateTransientLength N ρ.length
        · exact lift _ _ (by omega) (by omega) (Or.inl rfl) (Or.inl rfl) (by omega) (Or.inl hE)
        · have hM : 0 < Periodic.statePeriodModulus N ρ.length := by
            unfold Periodic.statePeriodModulus; positivity
          have hmlt := Nat.mod_lt (a' - Q'.start - Periodic.stateTransientLength N ρ.length) hM
          refine lift (b' - P'.start) (Periodic.stateTransientLength N ρ.length +
              (a' - Q'.start - Periodic.stateTransientLength N ρ.length) %
                Periodic.statePeriodModulus N ρ.length) (by omega) (by omega) (Or.inl rfl)
            (.inr ⟨by omega, by omega, ?_⟩) (by omega) (Or.inl hE)
          rw [Nat.add_mod_mod, show Periodic.stateTransientLength N ρ.length +
            (a' - Q'.start - Periodic.stateTransientLength N ρ.length) = a' - Q'.start by omega]
      · exfalso; omega
  · -- the first (partial) piece is complete: followers and the near/far choice of offsets
    have hQe : Q'.stop = a' + (P'.stop - b') := hQ'e' (by omega) (by omega) (by omega)
    have hfolN :=
        hx.canonicalCut_suffixComparison hN i j
            ((editedTuple W ρ N x j).length - (P'.stop - ρ.length))
      (P'.stop - ρ.length) (Q'.stop - ρ.length) rfl (by omega)
      (by have := hcmp.shift (P'.stop - ρ.length - b')
          rwa [show b' + (P'.stop - ρ.length - b') = P'.stop - ρ.length by omega,
            show a' + (P'.stop - ρ.length - b') = Q'.stop - ρ.length by omega] at this)
      (hP'l ▸ hx.nojun_end P' _) (hQ'l ▸ hx.nojun_end Q' _)
      (P.stop - ρ.length) (Q.stop - ρ.length) (hx.canonicalCut_end_sub_of_image_eq hP hP'l)
      (hx.canonicalCut_end_sub_of_image_eq hQ hQ'l)
    have hPlong := P.long; have hQlong := Q.long
    have hfol : SuffixComparison (W j) P.stop (W i) Q.stop := by
      have := hfolN.shift ρ.length
      rwa [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)] at this
    have hG : FollowerEdge P Q := Or.inl (by
      unfold Piece.follower; rw [hPl, hQl]; exact drop_prefix_iff_suffixComparison.mpr hfol)
    rcases hx.followerEdge_cases hPm hQm hG with hxe | ⟨hf1, hf1'⟩ | ⟨hf2, hf2'⟩
    · exact lift _ _ (by omega) (by omega) (Or.inl rfl) (Or.inl rfl)
        (by rw [hxe] at hLP; omega) (Or.inr ⟨by rw [hxe] at hLP; omega, hfol⟩)
    · -- far, target shorter: hold the target offset
      unfold Periodic.comparisonGap Periodic.boundaryMargin at hf1 hf1'
      exact lift (b' - P'.start) (b' - P'.start + (Q.len - P.len)) (by omega) (by omega)
        (Or.inl rfl) (.inr ⟨by omega, by omega, mod_eq_of_add_mul (u := x P) (v := x Q)
          (by omega)⟩) (by omega) (Or.inr ⟨by omega, hfol⟩)
    · -- far, host shorter: hold the host offset
      unfold Periodic.comparisonGap Periodic.boundaryMargin at hf2 hf2'
      exact lift (a' - Q'.start + (P.len - Q.len)) (a' - Q'.start) (by omega) (by omega)
        (.inr ⟨by omega, by omega, mod_eq_of_add_mul (u := x Q) (v := x P) (by omega)⟩)
        (Or.inl rfl) (by omega) (Or.inr ⟨by omega, hfol⟩)
private theorem suffixComparison_lift_of_no_piece {S : Type} [Fintype S] (T : Table α S k)
    (hNS : N = Fintype.card S)
    (hN : 0 < N) (i j : Fin k) {a' b' : ℕ} (ha' : a' ≤ (editedTuple W ρ N x i).length)
    (hb' : b' ≤ (editedTuple W ρ N x j).length)
    (hcmp : SuffixComparison (editedTuple W ρ N x j) b' (editedTuple W ρ N x i) a')
    (hα : ¬ (∃ P' : Piece (editedTuple W ρ N x) ρ.length, P'.coordinate = j ∧
      P' ∈ piecesOf (editedTuple W ρ N x) ρ ∧ P'.start ≤ b' ∧ b' + 2 * ρ.length < P'.stop)) :
    ∃ a ≤ (W i).length, ∃ b ≤ (W j).length, SuffixComparison (W j) b (W i) a ∧
      T.runPrefix W i a = T.runPrefix (editedTuple W ρ N x) i a' ∧ T.runPrefix W j b =
          T.runPrefix (editedTuple W ρ N x) j b' := by
  classical
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have h2d := Periodic.two_d_le_boundaryMargin hN ρ.length
  have hag : ∀ n < (editedTuple W ρ N x j).length - b',
      (editedTuple W ρ N x j)[b' + n]? = (editedTuple W ρ N x i)[a' + n]? :=
          fun n hn => hcmp n (by omega)
  have hag' : ∀ n < (editedTuple W ρ N x j).length - b',
      (editedTuple W ρ N x i)[a' + n]? = (editedTuple W ρ N x j)[b' + n]? :=
          fun n hn => (hag n hn).symm
  have hKc : Periodic.stateTransientLength N ρ.length + Periodic.statePeriodModulus N ρ.length ≤
      Periodic.comparisonGap N ρ.length := by
    unfold Periodic.comparisonGap Periodic.boundaryMargin; omega
  push Not at hα
  have hNJt : hx.NoInteriorJunction j b' ((editedTuple W ρ N x j).length - b') := by
    intro R hRl hxR h1 h2
    exfalso
    have := hα (hx.imagePiece R) hRl (hx.imagePiece_piece_mem hxR) h1
    have := hx.imagePiece_room hxR
    omega
  by_cases hNJh : hx.NoInteriorJunction i a' ((editedTuple W ρ N x j).length - b')
  · -- the backward expansion from the canonical cuts
    obtain ⟨b, hbc⟩ := hx.exists_canonicalCut j hb'
    obtain ⟨a, hac⟩ := hx.exists_canonicalCut i ha'
    exact
        ⟨a, hac.1, b, hbc.1,
            hx.canonicalCut_suffixComparison hN i j _ b' a' rfl hb' hcmp hNJt hNJh b a hbc hac,
      (hx.runPrefix_canonicalCut T hNS hac).symm, (hx.runPrefix_canonicalCut T hNS hbc).symm⟩
  · -- a short window inside a shortened host piece
    unfold NoInteriorJunction at hNJh
    push Not at hNJh
    obtain ⟨R, hRl, hxR, h1, h2, h3⟩ := hNJh
    have hroom := hx.imagePiece_room hxR
    have hR'm := hx.imagePiece_piece_mem hxR
    have hd := R.period_pos
    have hR'L := (hx.imagePiece R).start_add_len
    have hRe : a' + ((editedTuple W ρ N x j).length - b') ≤ (hx.imagePiece R).stop := by
      by_contra hlt
      have hRlt : (hx.imagePiece R).stop < (editedTuple W ρ N x i).length := by
        have := hcmp.lt_length (n := (hx.imagePiece R).stop - a') (by omega); omega
      obtain ⟨P'', h1', h2', h3', h4', _⟩ := copy_stretch hag' (hx.imagePiece R) hRl h1
        (ℓ := (hx.imagePiece R).stop - a') (by omega) (by omega) (by omega)
      exact absurd (hα P'' h1' (by rw [mem_piecesOf]; exact h4'.trans ((mem_piecesOf _).mp hR'm))
        h2') (by omega)
    have hn' : (editedTuple W ρ N x j).length - b' ≤ 2 * ρ.length := by
      by_contra hlt
      obtain ⟨P'', h1', h2', h3', h4', _⟩ := copy_stretch hag' (hx.imagePiece R) hRl h1
        (ℓ := (editedTuple W ρ N x j).length - b') (by omega) (by omega) le_rfl
      exact absurd (hα P'' h1' (by rw [mem_piecesOf]; exact h4'.trans ((mem_piecesOf _).mp hR'm))
        h2') (by omega)
    obtain ⟨b, hbc⟩ := hx.exists_canonicalCut j hb'
    obtain ⟨_, hkT, htT⟩ := hx.text_canonicalCut hbc (by omega)
      (hx.noJunction_window hNJt le_rfl fun R₂ hR₂l hxR₂ _ _ => by
        have := hx.imagePiece_room hxR₂
        have := (hx.imagePiece R₂).stop_le_length
        rw [show (hx.imagePiece R₂).coordinate = j from hR₂l] at this
        omega)
    have hpS : a' - (hx.imagePiece R).start ≤ retainedLength (N := N) (x := x) R := by
      have := hx.imagePiece_len R; omega
    have hale : R.start + (a' - (hx.imagePiece R).start) ≤ (W i).length := by
      have h1' := retainedLength_le (N := N) (x := x) R
      have h2' := R.stop_le_length
      have h3' := R.start_add_len
      have h4' := hx.imagePiece_len R
      rw [hRl] at h2'
      omega
    refine ⟨R.start + (a' - (hx.imagePiece R).start), hale, b, hbc.1, ?_, ?_,
      (hx.runPrefix_canonicalCut T hNS hbc).symm⟩
    · intro n hn
      have hnm : n < (editedTuple W ρ N x j).length - b' := by
        by_contra hge
        have :=
            hx.retainedCount_lt_length (l := j) (c := b + ((editedTuple W ρ N x j).length - b'))
                (by omega)
        rw [hkT, ← length_editedTuple] at this; omega
      have e :=
          hx.getElem?_imagePiece R (o := a' - (hx.imagePiece R).start + n)
              (by have := hx.imagePiece_len R; omega)
      rw [hRl, ← Nat.add_assoc, ← Nat.add_assoc,
        show (hx.imagePiece R).start + (a' - (hx.imagePiece R).start) = a' by omega] at e
      rw [htT n hnm, hag n hnm, e]
    · have := hx.runPrefix_imagePiece T hNS R hpS
      rw [hRl,
          show (hx.imagePiece R).start + (a' - (hx.imagePiece R).start) = a' by omega] at this
      exact this.symm
end AdmissibleDeletion
section Main
variable [DecidableEq α] {S : Type} [Fintype S] [DecidableEq S] {W : Fin k → List α}
  {ρ : List α} {x : Piece W ρ.length → ℕ}
end Main
section Holes
variable [DecidableEq α] {S : Type} [Fintype S] [DecidableEq S] {W : Fin k → List α}
  {ρ : List α} {x : Piece W ρ.length → ℕ}
section Site
variable {N dR : ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx
end Site
end Holes
end DeciSigma1.Holes.Periodic
end
end

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable [DecidableEq α] {W : Fin k → List α} {ρ : List α} {N : ℕ} {x : Piece W ρ.length → ℕ}
variable (hx : AdmissibleDeletion W ρ N x)
include hx
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution {S : Type} [Fintype S] (T : Table α S k) (hNS : N = Fintype.card S)
    (hN : 0 < N) (i j : Fin k) {a' b' : ℕ} (ha' : a' ≤ (editedTuple W ρ N x i).length)
    (hb' : b' ≤ (editedTuple W ρ N x j).length)
    (hcmp : SuffixComparison (editedTuple W ρ N x j) b' (editedTuple W ρ N x i) a') :
    ∃ a ≤ (W i).length, ∃ b ≤ (W j).length, SuffixComparison (W j) b (W i) a ∧
      T.runPrefix W i a = T.runPrefix (editedTuple W ρ N x) i a' ∧ T.runPrefix W j b =
          T.runPrefix (editedTuple W ρ N x) j b' := by
  classical
  by_cases hα : ∃ P' : Piece (editedTuple W ρ N x) ρ.length, P'.coordinate = j ∧
      P' ∈ piecesOf (editedTuple W ρ N x) ρ ∧ P'.start ≤ b' ∧ b' + 2 * ρ.length < P'.stop
  · exact hx.suffixComparison_lift_of_piece T hNS hN i j hb' hcmp hα
  · exact hx.suffixComparison_lift_of_no_piece T hNS hN i j ha' hb' hcmp hα
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
