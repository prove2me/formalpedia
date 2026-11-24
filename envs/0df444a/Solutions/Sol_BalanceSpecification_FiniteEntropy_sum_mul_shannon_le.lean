-- Prove2me | solution 1 for BalanceSpecification.FiniteEntropy.sum_mul_shannon_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:13:15.586524+00:00
-- url     : https://prove2.me/submissions/a1c6801c-3631-42d6-8031-8f97c3ca11f4

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_extensionPairs
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
open BalanceSpecification.FiniteEntropy
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
namespace BalanceSpecification.FiniteEntropy
theorem _root_.solution {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1)
    {p : κ → ι → ℝ} (hp : ∀ k i, 0 ≤ p k i) :
    ∑ k, w k * shannon (p k) ≤ shannon (fun i => ∑ k, w k * p k i) := by
  have hJ (i : ι) : ∑ k, w k * Real.negMulLog (p k i) ≤
      Real.negMulLog (∑ k, w k * p k i) := by
    simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.le_map_sum
      (t := Finset.univ) (fun k _ => hw k) hw1 (fun k _ => hp k i)
  calc
    ∑ k, w k * shannon (p k) = ∑ i, ∑ k, w k * Real.negMulLog (p k i) := by
      simp only [shannon, Real.negMulLog_def, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ i, Real.negMulLog (∑ k, w k * p k i) :=
      Finset.sum_le_sum (fun i _ => hJ i)
    _ = shannon (fun i => ∑ k, w k * p k i) := by
      simp only [shannon, Real.negMulLog_def]
end BalanceSpecification.FiniteEntropy
