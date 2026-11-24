-- Prove2me | solution 1 for FairSelling.CanonExists.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:44.12702+00:00
-- url     : https://prove2.me/submissions/1290b631-f8a9-4513-8cd7-e0958e52b8e1

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsProp6
import Definitions.Def_RequestProject_TwoThirdsGlue

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
namespace CanonExists
theorem _root_.solution {w p : G → ℝ} {μ t : ℝ} {k : ℕ} {R R' : Finset G} {D D' : ℝ}
    (hR : R ⊆ R') (hD : D ≤ D') (h : CanonExists w p μ t k R D) :
    CanonExists w p μ t k R' D' := by
  intro hk
  haveI : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk⟩
  obtain ⟨C⟩ := h hk
  exact ⟨{ C with
    goods_subset := fun j => (C.goods_subset j).trans hR
    sell_subset := C.sell_subset.trans hR
    dcash_sum := le_trans C.dcash_sum hD }⟩
end CanonExists
end FairSelling
