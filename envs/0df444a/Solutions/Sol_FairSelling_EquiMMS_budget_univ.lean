-- Prove2me | solution 1 for FairSelling.EquiMMS.budget_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:07:10.5894+00:00
-- url     : https://prove2.me/submissions/7876fe46-567f-441f-b13d-9c904805f9a3

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
namespace EquiMMS
theorem _root_.solution {w p : G → ℝ} {μ : ℝ} {k : ℕ} (E : EquiMMS w p μ k) :
    E.budget Finset.univ 0 = k * μ := by
  simp only [EquiMMS.budget, Finset.inter_univ, add_zero]
  rw [← E.cash_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun j _ => E.value j)]
  simp [mul_comm]
end EquiMMS
end FairSelling
