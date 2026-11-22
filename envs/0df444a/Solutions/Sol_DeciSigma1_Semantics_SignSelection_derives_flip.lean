-- Prove2me | solution 1 for DeciSigma1.Semantics.SignSelection.derives_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:28:52.787456+00:00
-- url     : https://prove2.me/submissions/f9b862e0-281e-4fa8-bb5d-38fa8bef2ee0

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Constraints.Signed
open DeciSigma1.Satisfiability
variable {n : ℕ} {V : Type*}
variable {ψ : List (LitT n (V × Bool))}
namespace DeciSigma1.Semantics.SignSelection
theorem _root_.solution (hc : FlipClosed ψ) {u v : (V × Bool)} (h : Derives ψ u v) :
    Derives ψ (flipV v) (flipV u) := by
  induction h with
  | refl => exact .refl _
  | lit hl => exact .lit (hc _ hl)
  | trans _ _ ih ih' => exact ih'.trans ih
  | decomp i hl _ hu ih => exact Derives.decomp i (hc _ hu) ih (hc _ hl)
end DeciSigma1.Semantics.SignSelection
