-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.site_deep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:38:47.535622+00:00
-- url     : https://prove2.me/submissions/19081fb2-1dc6-448e-a352-0db651ab03ec

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_boundaryMargin
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_deletedPositions
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_site_bound
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_not_mem_other
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α]
variable (W : Fin k → List α) (ρ : List α) (N : ℕ) (x : Piece W ρ.length → ℕ)
variable {W ρ N x}
namespace DeciSigma1.Holes.Periodic
namespace AdmissibleDeletion
theorem _root_.solution (hx : AdmissibleDeletion W ρ N x) {l : Fin k} {p : ℕ}
    (hp : p ∈ deletedPositions W ρ N x l) (Q : Piece W ρ.length) (hQl : Q.coordinate = l)
        (hQ1 : Q.start ≤ p)
    (hQ2 : p < Q.stop) : Q ∈ piecesOf W ρ ∧ x Q ≠ 0 ∧ Q.start + Periodic.boundaryMargin N ρ.length ≤
        p ∧
      p < Q.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length *
          x Q := by
  obtain ⟨P, hP, hPl, h1, h2⟩ := mem_deletedPositions.mp hp
  have hxP : x P ≠ 0 := by intro h0; rw [h0] at h2; omega
  have hb := hx.site_bound hxP
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hPQ : P = Q := by
    by_contra hne
    exact Piece.not_mem_other hne (hPl.trans hQl.symm) (p := p) (by omega) (by omega)
      ⟨hQ1, hQ2⟩
  subst hPQ
  exact ⟨hP, hxP, h1, h2⟩
end AdmissibleDeletion
end DeciSigma1.Holes.Periodic
