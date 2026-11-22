-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.deletedPositions_lt_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:50:55.438024+00:00
-- url     : https://prove2.me/submissions/3cc749cb-b643-4bbc-88e3-488c77643147

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_deletedPositions
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_site_bound

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
theorem _root_.solution (hx : AdmissibleDeletion W ρ N x) {l : Fin k}
    {p : ℕ}
    (hp : p ∈ deletedPositions W ρ N x l) : p < (W l).length := by
  obtain ⟨P, _, hPl, _, h2⟩ := mem_deletedPositions.mp hp
  have hxP : x P ≠ 0 := by intro h0; rw [h0] at h2; omega
  have := hx.site_bound hxP
  have := P.stop_le_length
  subst hPl
  omega
end AdmissibleDeletion
end DeciSigma1.Holes.Periodic
