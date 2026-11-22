-- Prove2me | solution 1 for DeciSigma1.Semantics.treeLe_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:39.496351+00:00
-- url     : https://prove2.me/submissions/49e1bafb-5b29-405f-b61d-08c24d2128a3

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
public import Theorems.Thm_DeciSigma1_Semantics_normalize_injective
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_iff_normalize

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
namespace DeciSigma1.Semantics
theorem _root_.solution {c : Fin n → Bool} {t u : Tree n}
    (htu : Le c t u) (hut : Le c u t) : t = u :=
  normalize_injective c false (_root_.le_antisymm ((treeLe_iff_normalize c t u).mp htu)
    ((treeLe_iff_normalize c u t).mp hut))
end DeciSigma1.Semantics
