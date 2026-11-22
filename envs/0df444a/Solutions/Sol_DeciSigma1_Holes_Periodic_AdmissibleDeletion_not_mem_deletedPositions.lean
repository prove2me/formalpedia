-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.not_mem_deletedPositions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:39:34.991056+00:00
-- url     : https://prove2.me/submissions/564d8a76-740d-4bb8-94c3-22ee192d1032

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_site_deep

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
    (Q : Piece W ρ.length) (hQl : Q.coordinate = l) (hQ1 : Q.start ≤ p) (hQ2 : p < Q.stop)
    (hns : p < Q.start + Periodic.boundaryMargin N ρ.length ∨ Q.start + Periodic.boundaryMargin N
        ρ.length + Periodic.statePeriodModulus N ρ.length * x Q ≤ p) :
    p ∉ deletedPositions W ρ N x l := by
  intro hp
  have := hx.site_deep hp Q hQl hQ1 hQ2
  omega
end AdmissibleDeletion
end DeciSigma1.Holes.Periodic
