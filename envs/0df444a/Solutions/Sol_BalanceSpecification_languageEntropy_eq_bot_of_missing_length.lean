-- Prove2me | solution 1 for BalanceSpecification.languageEntropy_eq_bot_of_missing_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:38.849604+00:00
-- url     : https://prove2.me/submissions/a80eac19-615e-435a-a0ce-2cccd533f83f

module
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Theorems.Thm_BalanceSpecification_wordCount_eq_zero_of_le_missing

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open scoped ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A]
omit [TopologicalSpace A] [DiscreteTopology A]
namespace BalanceSpecification
theorem _root_.solution {L : Set (Word A)}
    (hL : IsFactorial L) {N : ℕ} (hN : wordCount L N = 0) : languageEntropy L = ⊥ := by
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log ((wordCount L (n + 1) : ℕ) : ℝ≥0∞)) = ⊥ := by
    apply (Filter.eventually_ge_atTop N).mono
    intro n hn
    have hz := wordCount_eq_zero_of_le_missing hL (show N ≤ n + 1 by omega) hN
    rw [hz, Nat.cast_zero, ENNReal.log_zero]
    exact EReal.coe_mul_bot_of_pos (inv_pos.mpr (by exact_mod_cast Nat.succ_pos n))
  have ht : Filter.Tendsto (fun n : ℕ =>
      (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log ((wordCount L (n + 1) : ℕ) : ℝ≥0∞))) Filter.atTop (nhds ⊥) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [hevent] with n hn
      exact hn.symm)
  exact ht.limsup_eq
end BalanceSpecification
