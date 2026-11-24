-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleFour.val_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mceppaglia
-- created : 2026-11-24T02:04:10.694999+00:00
-- url     : https://prove2.me/submissions/ca3fde19-117e-4220-b62b-d6c775a9db20

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)
theorem solution (L : ℝ) {i : Fin (N + 2)} (hi : i ≠ 0) : val N L i = fun _ => L := by
  funext g
  exact if_neg hi
