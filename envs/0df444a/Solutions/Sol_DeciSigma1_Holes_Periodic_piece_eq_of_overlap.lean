-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.piece_eq_of_overlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:55:34.106519+00:00
-- url     : https://prove2.me/submissions/0c5a63e0-d2d1-4a38-8bb4-0c87f9e950be

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_periodicOn
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_union


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
variable {W : Fin k → List α} {d : ℕ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution {P Q : Piece W d} (hl : P.coordinate = Q.coordinate)
    (h₁ : P.start + d ≤ Q.stop)
    (h₂ : Q.start + d ≤ P.stop) : P = Q := by
  have hQper : PeriodicOn (W P.coordinate) d Q.start Q.stop := hl ▸ Q.periodic
  have hQle : Q.stop ≤ (W P.coordinate).length := hl ▸ Q.stop_le_length
  have hQL : Q.start = 0 ∨ (W P.coordinate)[Q.start - 1]? ≠ (W P.coordinate)[Q.start - 1 + d]? :=
      hl ▸ Q.left_maximal
  have hQR : Q.stop = (W P.coordinate).length ∨ (W P.coordinate)[Q.stop]? ≠
      (W P.coordinate)[Q.stop - d]? := hl ▸ Q.right_maximal
  have hP := P.long; have hQ := Q.long
  -- the union of the two stretches is periodic
  have hU : PeriodicOn (W P.coordinate) d (min P.start Q.start) (max P.stop Q.stop) := by
    rcases le_total P.start Q.start with h | h
    · rw [min_eq_left h]; exact P.periodicOn.union hQper h₂
    · rw [min_eq_right h, max_comm]; exact hQper.union P.periodicOn h₁
  have he : P.stop = Q.stop := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · rcases P.right_maximal with h | h
      · omega
      · apply h
        have := hU (P.stop - d) (by omega) (by omega)
        rw [show P.stop - d + d = P.stop by omega] at this
        exact this.symm
    · rcases hQR with h | h
      · have := P.stop_le_length; omega
      · apply h
        have := hU (Q.stop - d) (by omega) (by omega)
        rw [show Q.stop - d + d = Q.stop by omega] at this
        exact this.symm
  have hs : P.start = Q.start := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · rcases hQL with h | h
      · omega
      · exact h (hU (Q.start - 1) (by omega) (by omega))
    · rcases P.left_maximal with h | h
      · omega
      · exact h (hU (P.start - 1) (by omega) (by omega))
  exact Piece.ext_coordinates hl hs he
end DeciSigma1.Holes.Periodic
