-- Prove2me | solution 1 for FairSelling.canonExists_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:13:24.544928+00:00
-- url     : https://prove2.me/submissions/48d68b10-7d34-4823-92cc-d255c786f35b

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
theorem _root_.solution {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}
    (h : Nonempty (Canonical w p μ t k R D)) : CanonExists w p μ t k R D :=
  fun _ => h
end FairSelling
