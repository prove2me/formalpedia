-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_suffixComparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:53:10.91053+00:00
-- url     : https://prove2.me/submissions/ab6a4a0f-dd01-4004-9262-fe6278f0b368

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_drop_prefix_iff_suffixComparison
public import Theorems.Thm_DeciSigma1_Holes_Periodic_SuffixComparison_shift
public import Theorems.Thm_DeciSigma1_Holes_Periodic_SuffixComparison_lt_length
public import Theorems.Thm_DeciSigma1_Holes_Periodic_SuffixComparison_append
public import Theorems.Thm_DeciSigma1_Holes_Periodic_copy_piece
public import Theorems.Thm_DeciSigma1_Holes_Periodic_piece_suffixComparison
public import Theorems.Thm_P2M_DeciSigma1_Holes_Periodic_getElem__eq_of_root_eq_400ed337ec00
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_piece_mem
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_nojun_end
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_target_piece_of_junction
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_le_length
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_start_of_image_eq
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_end_sub_of_image_eq
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_noJunction_window
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_add
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_unique
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_eq_of_followerEdge
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_exists_imagePiece
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_len
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_mem_iff
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_root
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop_eq_length_iff
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_len_le_of_followerEdge
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_length_editedTuple
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_retainedCount_lt_length
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_text_canonicalCut
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_len_ge
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_boundaryMargin
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_piecesOf
public import Theorems.Thm_DeciSigma1_Holes_Periodic_two_d_le_boundaryMargin


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
theorem _root_.solution (hN : 0 < N) (i j : Fin k) (m : ℕ) :
    ∀ ct' ch', (editedTuple W ρ N x j).length - ct' = m → ct' ≤ (editedTuple W ρ N x j).length →
      SuffixComparison (editedTuple W ρ N x j) ct' (editedTuple W ρ N x i) ch' →
          hx.NoInteriorJunction j ct' m →
      hx.NoInteriorJunction i ch' m → ∀ ct ch,
        CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) j ct ct' →
        CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) i ch ch' →
      SuffixComparison (W j) ct (W i) ch := by
  classical
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro ct' ch' hm hct hcmp hNJt hNJh ct ch hctc hchc
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have h2d := Periodic.two_d_le_boundaryMargin hN ρ.length
  have hch' := canonicalCut_le_length hchc
  have hag : ∀ n < m, (editedTuple W ρ N x j)[ct' + n]? = (editedTuple W ρ N x i)[ch' + n]? :=
    fun n hn => hcmp n (by omega)
  by_cases hex : ∃ P' : Piece (editedTuple W ρ N x) ρ.length, P'.coordinate = j ∧
      P' ∈ piecesOf (editedTuple W ρ N x) ρ ∧ ct' < P'.start
  · -- the next class piece of the target
    have hexs : ∃ s₀, ∃ P' : Piece (editedTuple W ρ N x) ρ.length, P'.coordinate = j ∧
        P' ∈ piecesOf (editedTuple W ρ N x) ρ ∧ ct' < P'.start ∧ P'.start = s₀ := by
      obtain ⟨P', h1, h2, h3⟩ := hex; exact ⟨P'.start, P', h1, h2, h3, rfl⟩
    obtain ⟨P', hP'l, hP'm, hP's, hP's0⟩ := Nat.find_spec hexs
    have hmin : ∀ P'' : Piece (editedTuple W ρ N x) ρ.length, P''.coordinate = j →
        P'' ∈ piecesOf (editedTuple W ρ N x) ρ → ct' < P''.start → P'.start ≤ P''.start := by
      intro P'' h1 h2 h3; rw [hP's0]; exact Nat.find_min' hexs ⟨P'', h1, h2, h3, rfl⟩
    have hP'e := P'.stop_le_length; rw [hP'l] at hP'e
    have hd := P'.period_pos
    have hP'L := P'.start_add_len
    have hP'g := P'.len_ge
    -- the matched host piece
    obtain ⟨Q', hQ'l, hQ's, hQ'root, hQ'e, hQ'e'⟩ := copy_piece hag P' hP'l hP's
      (ℓ := P'.len) hP'g (by omega) (by omega)
    have hQ'm : Q' ∈ piecesOf (editedTuple W ρ N x) ρ := by
      rw [mem_piecesOf, hQ'root]; exact (mem_piecesOf _).mp hP'm
    obtain ⟨P, hP⟩ := hx.exists_imagePiece P'
    obtain ⟨Q, hQ⟩ := hx.exists_imagePiece Q'
    have hPl : P.coordinate = j := by rw [← hP'l, ← hP]; rfl
    have hQl : Q.coordinate = i := by rw [← hQ'l, ← hQ]; rfl
    have hPm : P ∈ piecesOf W ρ := (hx.imagePiece_mem_iff P).mp (hP ▸ hP'm)
    have hQm : Q ∈ piecesOf W ρ := (hx.imagePiece_mem_iff Q).mp (hQ ▸ hQ'm)
    have hQ'le := Q'.stop_le_length; rw [hQ'l] at hQ'le
    have hQ'L := Q'.start_add_len
    -- the unchanged region before the pieces, on both sides: a later junction of the target
    -- belongs to a class piece starting after `P'`, one of the host gives such a piece
    obtain ⟨hcT, htT⟩ := hx.canonicalCut_add hctc (n := P'.start - ct') (by omega)
      (hx.noJunction_window hNJt (by omega) fun R hRl hxR h1 h2 => by
        have := hmin (hx.imagePiece R) hRl (hx.imagePiece_piece_mem hxR) h1; omega)
    obtain ⟨hcH, htH⟩ := hx.canonicalCut_add hchc (n := P'.start - ct') (by omega)
      (hx.noJunction_window hNJh (by omega) fun R hRl hxR h1 h2 => by
        obtain ⟨P'', h1', h2', h3'⟩ := hx.target_piece_of_junction hN hcmp R hRl hxR h1 (by omega)
        have := hmin P'' h1' h2' (by omega); omega)
    rw [show ct' + (P'.start - ct') = P'.start by omega] at hcT
    rw [show ch' + (P'.start - ct') = Q'.start by omega] at hcH
    have hctr : ct + (P'.start - ct') = P.start :=
        canonicalCut_unique hcT (hx.canonicalCut_start_of_image_eq hP hP'l)
    have hchr : ch + (P'.start - ct') = Q.start :=
        canonicalCut_unique hcH (hx.canonicalCut_start_of_image_eq hQ hQ'l)
    have hreg : ∀ n < P'.start - ct', (W j)[ct + n]? = (W i)[ch + n]? := by
      intro n hn; rw [htT n hn, hag n (by omega), ← htH n hn]
    -- the piece step
    have hnP : retainedLength (N := N) (x := x) P = P'.len := by rw [← hx.imagePiece_len, hP]
    have hnQ : retainedLength (N := N) (x := x) Q = Q'.len := by rw [← hx.imagePiece_len, hQ]
    have hroot : P.root = Q.root := by
      rw [← hx.imagePiece_root P, ← hx.imagePiece_root Q, hP, hQ, hQ'root]
    have hstep : SuffixComparison (W j) P.start (W i) Q.start := by
      by_cases hterm : P'.stop = (editedTuple W ρ N x j).length
      · have hE : P.stop = (W P.coordinate).length := (hx.imagePiece_stop_eq_length_iff P).mp (by
          rw [hP, hterm, hPl])
        have hG : FollowerEdge P Q := Or.inl (by
          unfold Piece.follower; rw [hE, List.drop_length]; exact List.nil_prefix)
        have hle := hx.len_le_of_followerEdge hPm hQm hG (by omega)
        have := piece_suffixComparison P Q (oP := 0) (oQ := 0) (by omega) (by omega)
          (getElem?_eq_of_root_eq P Q hroot) (by omega) (Or.inl hE)
        rwa [hPl, hQl, Nat.add_zero, Nat.add_zero] at this
      · have hQe : Q'.stop = ch' + (P'.stop - ct') := hQ'e' (by omega) (by omega)
        have hfolN := ih ((editedTuple W ρ N x j).length - (P'.stop - ρ.length)) (by omega)
          (P'.stop - ρ.length) (Q'.stop - ρ.length) rfl (by omega)
          (by have := hcmp.shift (P'.stop - ρ.length - ct')
              rwa [show ct' + (P'.stop - ρ.length - ct') = P'.stop - ρ.length by omega,
                show ch' + (P'.stop - ρ.length - ct') = Q'.stop - ρ.length by omega] at this)
          (hP'l ▸ hx.nojun_end P' _) (hQ'l ▸ hx.nojun_end Q' _)
          (P.stop - ρ.length) (Q.stop - ρ.length) (hx.canonicalCut_end_sub_of_image_eq hP hP'l)
          (hx.canonicalCut_end_sub_of_image_eq hQ hQ'l)
        have hPe := P.long; have hQe2 := Q.long
        have hfol : SuffixComparison (W j) P.stop (W i) Q.stop := by
          have := hfolN.shift ρ.length
          rwa [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)] at this
        have hG : FollowerEdge P Q := Or.inl (by
          unfold Piece.follower; rw [hPl, hQl]; exact drop_prefix_iff_suffixComparison.mpr hfol)
        have heq := (hx.eq_of_followerEdge hPm hQm hG (by omega)).2
        have := piece_suffixComparison P Q (oP := 0) (oQ := 0) (by omega) (by omega)
          (getElem?_eq_of_root_eq P Q hroot) (by omega)
          (Or.inr ⟨by omega, by rw [hPl, hQl]; exact hfol⟩)
        rwa [hPl, hQl, Nat.add_zero, Nat.add_zero] at this
    exact SuffixComparison.append hreg (by rw [hctr, hchr]; exact hstep)
  · -- no further class piece of the target: the rest is unchanged text on both sides
    push Not at hex
    have hJt := hx.noJunction_window hNJt le_rfl fun R hRl hxR h1 _ =>
      absurd (hex (hx.imagePiece R) hRl (hx.imagePiece_piece_mem hxR)) (by omega)
    have hJh := hx.noJunction_window hNJh le_rfl fun R hRl hxR h1 h2 => by
      obtain ⟨P'', h1', h2', h3'⟩ := hx.target_piece_of_junction hN hcmp R hRl hxR h1 (by omega)
      exact absurd (hex P'' h1' h2') (by omega)
    have hhn : ch' + m ≤ (editedTuple W ρ N x i).length := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · omega
      · have := hcmp.lt_length (n := m - 1) (by omega); omega
    obtain ⟨_, hkT, htT⟩ := hx.text_canonicalCut hctc (by omega) hJt
    have htH := (hx.text_canonicalCut hchc hhn hJh).2.2
    intro n hn
    have hnm : n < m := by
      by_contra hge
      have := hx.retainedCount_lt_length (l := j) (c := ct + m) (by omega)
      rw [hkT, ← length_editedTuple] at this; omega
    rw [htT n hnm, hag n hnm, ← htH n hnm]
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
