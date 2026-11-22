-- Prove2me | solution 1 for DeciSigma1.Semantics.SignSelection.lowerAt_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:29:50.681197+00:00
-- url     : https://prove2.me/submissions/18943640-5fa9-47a0-aab1-dc2199e3f718

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_derives_flip

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Constraints.Signed
open DeciSigma1.Satisfiability
variable {n : ℕ} {V : Type*}
variable {ψ : List (LitT n (V × Bool))}
namespace DeciSigma1.Semantics.SignSelection
theorem _root_.solution (hc : FlipClosed ψ) {π : List (Fin n)} {x y : (V × Bool)}
    (h : LowerAt ψ π x y) : UpperAt ψ π (flipV y) (flipV x) := by
  induction h with
  | nil hd => exact .nil (derives_flip hc hd)
  | cons hl hd _ ih => exact .cons (derives_flip hc hd) (hc _ hl) ih
end DeciSigma1.Semantics.SignSelection
