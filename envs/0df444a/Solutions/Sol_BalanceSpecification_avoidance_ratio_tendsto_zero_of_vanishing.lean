-- Prove2me | solution 1 for BalanceSpecification.avoidance_ratio_tendsto_zero_of_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:25.310041+00:00
-- url     : https://prove2.me/submissions/5a72666d-0d64-42ac-b3b0-fe3284657997

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Theorems.Thm_BalanceSpecification_wordCount_eq_zero_of_le

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution (hL : IsFactorial L)
    (v : Word A) {m : ℕ} (hm : wordCount (avoidingLanguage L v) m = 0) :
    Tendsto
      (fun n : ℕ => (wordCount (avoidingLanguage L v) n : ℝ) / wordCount L n)
      atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop m] with n hn
  rw [wordCount_eq_zero_of_le (hL.avoidingLanguage v) hm hn, Nat.cast_zero, zero_div]
end BalanceSpecification
