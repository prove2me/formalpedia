-- Prove2me | solution 1 for FairSelling.pair_acceptable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:14:22.166241+00:00
-- url     : https://prove2.me/submissions/64caedba-a3c5-4fb3-b1c1-79375f4a48ef

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsProp6
import Definitions.Def_RequestProject_TwoThirdsGlue
import Definitions.Def_RequestProject_TwoThirdsDescent

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) {ε : ℝ} {d₁ d₂ : G} (hne : d₁ ≠ d₂)
    (h₁ : ε ≤ vbar w p d₁) (h₂ : ε ≤ vbar w p d₂) :
    2 * ε ≤ vbarSum w p {d₁, d₂} := by
  rw [vbarSum, Finset.sum_pair hne]
  linarith
end FairSelling
