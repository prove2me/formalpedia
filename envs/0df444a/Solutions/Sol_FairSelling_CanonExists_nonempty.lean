-- Prove2me | solution 1 for FairSelling.CanonExists.nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:13:09.533749+00:00
-- url     : https://prove2.me/submissions/1b2dfa62-04a3-4622-9494-eebd0f588972

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
theorem _root_.solution {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}
    (h : CanonExists w p μ t k R D) : Nonempty (Canonical w p μ t k R D) :=
  h (Nat.pos_of_ne_zero (NeZero.ne k))
end CanonExists
end FairSelling
