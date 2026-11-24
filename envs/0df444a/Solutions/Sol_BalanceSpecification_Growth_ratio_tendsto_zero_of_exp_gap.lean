-- Prove2me | solution 1 for BalanceSpecification.Growth.ratio_tendsto_zero_of_exp_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:49.173206+00:00
-- url     : https://prove2.me/submissions/bfbb098d-4ac7-4806-84aa-ddfd9cdec613

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Theorems.Thm_BalanceSpecification_mem_avoidingLanguage
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
theorem _root_.solution {a b : ℕ → ℝ} {α β : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hgap : α < β)
    (hupper : ∀ᶠ n : ℕ in atTop, a n ≤ Real.exp ((n : ℝ) * α))
    (hlower : ∀ n : ℕ, Real.exp ((n : ℝ) * β) ≤ b n) :
    Tendsto (fun n => a n / b n) atTop (𝓝 0) := by
  have hb n : 0 < b n := (Real.exp_pos _).trans_le (hlower n)
  have hexp : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (α - β)))
      atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have ht : Tendsto (fun n : ℕ => (α - β) * (n : ℝ)) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (sub_neg.mpr hgap)).mpr
        tendsto_natCast_atTop_atTop
    simpa only [mul_comm] using ht
  apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (ha n) (hb n).le) ?_ hexp
  filter_upwards [hupper] with n hn
  calc
    a n / b n ≤ Real.exp ((n : ℝ) * α) / b n :=
      div_le_div_of_nonneg_right hn (hb n).le
    _ ≤ Real.exp ((n : ℝ) * α) / Real.exp ((n : ℝ) * β) :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (Real.exp_pos _) (hlower n)
    _ = Real.exp ((n : ℝ) * (α - β)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
end BalanceSpecification.Growth
