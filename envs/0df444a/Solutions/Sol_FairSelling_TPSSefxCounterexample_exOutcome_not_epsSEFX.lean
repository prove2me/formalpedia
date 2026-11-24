-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exOutcome_not_epsSEFX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:10.154442+00:00
-- url     : https://prove2.me/submissions/0030d77d-d40b-48a3-b366-94e39309d1ca

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxExamples
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_one
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_two
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_three
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_one
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_two
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_three
import Theorems.Thm_FairSelling_TPSSefxCounterexample_sum23
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_one
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_two
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_three
attribute [local simp] FairSelling.TPSSefxCounterexample.exp_one
attribute [local simp] FairSelling.TPSSefxCounterexample.exp_two
attribute [local simp] FairSelling.TPSSefxCounterexample.exp_three

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.TPSSefxCounterexample
namespace FairSelling.TPSSefxCounterexample
theorem _root_.solution (eps : ℝ) : ¬ epsSEFX exV exp eps exOutcome := by
  intro h
  have h10 := (h 1 0).1 (by norm_num [exOutcome])
  have hlhs : vbarSum (exV 1) exp (exOutcome.kept 1) + exOutcome.money 1 = 24 := by
    show (∑ g ∈ ({2, 3} : Finset Gd), vbar exv exp g) + 0 = 24
    rw [sum23]
    unfold vbar
    norm_num [exv_two, exv_three, exp_two, exp_three]
  have hrhs : vbarSum (exV 1) exp (exOutcome.kept 0) + exOutcome.money 0 = 36 := by
    show (∑ g ∈ ({1} : Finset Gd), vbar exv exp g) + 18 = 36
    unfold vbar
    norm_num [exv_one, exp_one]
  rw [hlhs, hrhs] at h10
  norm_num at h10
end FairSelling.TPSSefxCounterexample
