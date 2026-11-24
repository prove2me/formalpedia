-- Prove2me | solution 1 for BalanceSpecification.Growth.ratio_tendsto_zero_of_rate_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:52.216841+00:00
-- url     : https://prove2.me/submissions/0bb82f3f-7064-4413-b63d-2b32fb9c9afc

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Theorems.Thm_BalanceSpecification_mem_avoidingLanguage
public import Theorems.Thm_BalanceSpecification_Growth_ratio_tendsto_zero_of_exp_gap
public import Theorems.Thm_BalanceSpecification_Growth_tendsto_rate
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset


attribute [local simp] BalanceSpecification.mem_avoidingLanguage

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] {L : Set (Word A)}
open BalanceSpecification.Growth
namespace BalanceSpecification.Growth
theorem _root_.solution {a b : ℕ → ℝ} {β : ℝ}
    (ha : ∀ n, 1 ≤ a n) (hsa : Submultiplicative a)
    (hgap : rate a < β) (hlower : ∀ n : ℕ, Real.exp ((n : ℝ) * β) ≤ b n) :
    Tendsto (fun n => a n / b n) atTop (𝓝 0) := by
  let α : ℝ := (rate a + β) / 2
  have hα : rate a < α := by dsimp only [α]; linarith only [hgap]
  have hαβ : α < β := by dsimp only [α]; linarith only [hgap]
  have hsmall : ∀ᶠ n : ℕ in atTop, Real.log (a n) / n < α :=
    (tendsto_rate ha hsa).eventually (gt_mem_nhds hα)
  apply ratio_tendsto_zero_of_exp_gap (fun n => zero_le_one.trans (ha n)) hαβ ?_ hlower
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  calc
    a n = Real.exp (Real.log (a n)) := (Real.exp_log (zero_lt_one.trans_le (ha n))).symm
    _ ≤ Real.exp ((n : ℝ) * α) := Real.exp_le_exp.mpr
      (by simpa only [mul_comm] using ((div_lt_iff₀ hnpos).mp hn).le)
end BalanceSpecification.Growth
