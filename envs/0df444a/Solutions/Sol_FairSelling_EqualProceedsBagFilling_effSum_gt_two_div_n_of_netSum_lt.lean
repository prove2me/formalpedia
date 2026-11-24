-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.effSum_gt_two_div_n_of_netSum_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:56:02.120295+00:00
-- url     : https://prove2.me/submissions/c3210e33-0c49-43f3-aaf4-68696c9484bb

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_remarkPrice_nonneg
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_remarkTPS

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}
namespace FairSelling.EqualProceedsBagFilling
theorem _root_.solution :
    ∃ (val pr : Fin 10 → ℝ) (e : Fin 10) (t : ℝ),
      (∀ g, 0 ≤ val g) ∧ (∀ g, 0 ≤ pr g) ∧ t = TPS 10 val pr ∧
      pr e < t ∧ val e < t / 10 ∧
      netSum 10 val pr t {e} < t / 10 ∧
      (2 / 10) * t < effSum val pr t {e} := by
  refine ⟨fun _ => 0, remarkPrice, 0, 99 / 100, fun _ => le_rfl, remarkPrice_nonneg,
    remarkTPS.symm, ?_, ?_, ?_, ?_⟩
  · norm_num [remarkPrice]
  · norm_num
  · rw [netSum, Finset.sum_singleton, netVal]
    norm_num [remarkPrice]
  · rw [effSum, Finset.sum_singleton, effVal]
    norm_num [remarkPrice]
end FairSelling.EqualProceedsBagFilling
