-- Prove2me | solution 1 for DeciSigma1.Semantics.normalize_fn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:35:04.276286+00:00
-- url     : https://prove2.me/submissions/41d4186d-ee74-4da5-b715-807545aa8403

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
namespace DeciSigma1.Semantics
theorem _root_.solution (c : Fin n → Bool) (p : Bool) (t : Tree n) (π : List (Fin n)) :
    (Tree.normalize c p t).fn π = (t.fn π).map (Sym.flip (Bool.xor p (polarity c π))) := rfl
end DeciSigma1.Semantics
