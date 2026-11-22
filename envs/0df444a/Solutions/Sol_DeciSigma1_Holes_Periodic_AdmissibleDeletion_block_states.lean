-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.block_states
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:44:47.274523+00:00
-- url     : https://prove2.me/submissions/5ff57e38-3937-4bc2-985b-8bd4d3bf98a2

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_runPrefix_add_mul
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_site_bound
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_boundaryMargin
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_deletedPositions


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable {N : ℕ} {x : Piece W ρ.length → ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx
variable [Fintype S] (T : Table α S k) (hN : N = Fintype.card S)
include hN
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution (l : Fin k) :
    ∀ j c, j < c → c ≤ (W l).length → (∀ p, j ≤ p → p < c → p ∈ deletedPositions W ρ N x l) →
      (j = 0 ∨ j - 1 ∉ deletedPositions W ρ N x l) → c ∉ deletedPositions W ρ N x l →
      runFrom T.step (T.start l) ((W l).take j) = runFrom T.step (T.start l) ((W l).take c) := by
  intro j c hjc hc hD hj hcD
  obtain ⟨P, hP, hPl, h1, h2⟩ := mem_deletedPositions.mp (hD (c - 1) (by omega) (by omega))
  subst hPl
  have hxP : x P ≠ 0 := by intro h0; rw [h0] at h2; omega
  have hb := hx.site_bound hxP
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hd := P.period_pos
  have hcE : c = P.start + Periodic.boundaryMargin N ρ.length +
      Periodic.statePeriodModulus N ρ.length * x P := by
    by_contra hne
    exact hcD (hx.site_sub (by omega) (by omega))
  have hjE : j = P.start + Periodic.boundaryMargin N ρ.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hx.in_piece_not_mem P (p := P.start + Periodic.boundaryMargin N ρ.length - 1) (by omega)
        (by omega)
        (Or.inl (by omega)) (hD _ (by omega) (by omega))
    · rcases hj with h' | h'
      · omega
      · exact h' (hx.site_sub (by omega) (by omega))
  subst hcE hjE
  have := P.runPrefix_add_mul T (o := Periodic.boundaryMargin N ρ.length) (m := x P)
    (by rw [← hN]; unfold Periodic.boundaryMargin Periodic.stateTransientLength; omega)
    (by rw [← hN]; unfold Piece.len; unfold Periodic.statePeriodModulus at hb; rw [mul_comm (x P)];
        omega)
  unfold runPrefix at this
  rw [← this, hN, Periodic.statePeriodModulus, mul_comm (x P)]
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
