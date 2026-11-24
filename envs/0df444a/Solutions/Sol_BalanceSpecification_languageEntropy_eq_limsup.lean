-- Prove2me | solution 1 for BalanceSpecification.languageEntropy_eq_limsup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:57:31.673843+00:00
-- url     : https://prove2.me/submissions/bb709880-4078-4b1b-b4b6-aa556e4c4c7e

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
theorem _root_.solution (L : Set (Word A)) :
    languageEntropy L = Filter.limsup (fun n : ℕ =>
      ((((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log ((wordCount L n : ℕ) : ℝ≥0∞)))
        Filter.atTop := by
  unfold languageEntropy
  change Filter.limsup ((fun n : ℕ =>
      ((((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log ((wordCount L n : ℕ) : ℝ≥0∞))) ∘
        (fun n : ℕ => n + 1)) Filter.atTop = _
  rw [Filter.limsup_comp, Filter.map_add_atTop_eq_nat]
end BalanceSpecification
