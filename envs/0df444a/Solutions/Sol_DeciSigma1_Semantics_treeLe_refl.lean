-- Prove2me | solution 1 for DeciSigma1.Semantics.treeLe_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:48.173582+00:00
-- url     : https://prove2.me/submissions/2690cfc5-18ba-4a6a-89d2-d14fb17549df

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_iff_normalize

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
namespace DeciSigma1.Semantics
theorem _root_.solution (c : Fin n → Bool) (t : Tree n) : Le c t t :=
  (treeLe_iff_normalize c t t).mpr le_rfl
end DeciSigma1.Semantics
