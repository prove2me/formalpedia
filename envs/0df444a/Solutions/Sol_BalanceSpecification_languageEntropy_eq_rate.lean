-- Prove2me | solution 1 for BalanceSpecification.languageEntropy_eq_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:10.316744+00:00
-- url     : https://prove2.me/submissions/0634026f-fa75-4826-9d21-e294bee5a6d1

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
public import Theorems.Thm_BalanceSpecification_Growth_tendsto_rate
public import Theorems.Thm_BalanceSpecification_wordCount_add_le


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
theorem _root_.solution {L : Set (Word A)} (hL : IsFactorial L)
    (hpos : ∀ n, 0 < wordCount L n) :
    languageEntropy L = (Growth.rate (fun n => (wordCount L n : ℝ)) : EReal) := by
  have ha : ∀ n, (1 : ℝ) ≤ wordCount L n := fun n => by exact_mod_cast hpos n
  have hs : Submultiplicative (fun n => (wordCount L n : ℝ)) := by
    intro m n
    change (wordCount L (m + n) : ℝ) ≤ (wordCount L m : ℝ) * (wordCount L n : ℝ)
    exact_mod_cast wordCount_add_le hL m n
  have ht := continuous_coe_real_ereal.continuousAt.tendsto.comp
    ((Growth.tendsto_rate ha hs).comp (Filter.tendsto_add_atTop_nat 1))
  have hseq (n : ℕ) :
      (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log ((wordCount L (n + 1) : ℕ) : ℝ≥0∞)) =
      ((Real.log (wordCount L (n + 1)) / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal) := by
    have hn : (0 : ℝ) < wordCount L (n + 1) := by exact_mod_cast hpos (n + 1)
    rw [← ENNReal.ofReal_natCast, ENNReal.log_ofReal_of_pos hn, ← EReal.coe_mul]
    congr 1
    exact mul_comm _ _
  exact (ht.congr' (Filter.Eventually.of_forall fun n => (hseq n).symm)).limsup_eq
end BalanceSpecification
