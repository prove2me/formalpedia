-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.site_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:45:40.085785+00:00
-- url     : https://prove2.me/submissions/504268f2-dc3f-4818-a39f-3ec52f8d406a

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion

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
theorem _root_.solution (hx : AdmissibleDeletion W ρ N x) {P : Piece W ρ.length}
    (hP : x P ≠ 0) :
    P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x P +
        (5 * Periodic.boundaryMargin N ρ.length +
      2 * Periodic.statePeriodModulus N ρ.length) ≤ P.stop := by
  have := hx.long P (hx.supp P hP) hP
  have := P.long
  unfold Piece.len Periodic.fixedMargin at *
  omega
end AdmissibleDeletion
end DeciSigma1.Holes.Periodic
