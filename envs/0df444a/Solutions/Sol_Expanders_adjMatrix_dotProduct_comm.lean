-- Prove2me | solution 1 for Expanders.adjMatrix_dotProduct_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:18:59.487802+00:00
-- url     : https://prove2.me/submissions/af6ab90c-57e4-4253-b477-172424992279

module
public import Mathlib
public import Definitions.Def_ExpanderLib_MixingAux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix
open Expanders
variable {V : Type*} [Fintype V]
namespace Expanders
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V → ℝ) :
    dotProduct x (G.adjMatrix ℝ *ᵥ y) = dotProduct y (G.adjMatrix ℝ *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, (isSymm_adjMatrix G).eq, dotProduct_comm]
end Expanders
