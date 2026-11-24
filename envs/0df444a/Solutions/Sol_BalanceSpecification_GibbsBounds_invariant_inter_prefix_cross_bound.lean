-- Prove2me | solution 1 for BalanceSpecification.GibbsBounds.invariant_inter_prefix_cross_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:17:21.147329+00:00
-- url     : https://prove2.me/submissions/855f9b75-52b3-4726-93bc-9becdf565469

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Theorems.Thm_BalanceSpecification_GibbsBounds_invariant_inter_prefix_bound
public import Theorems.Thm_BalanceSpecification_GibbsBounds_quasiBernoulli
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
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
open MeasureTheory Set
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [Fintype A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
namespace GibbsBounds
theorem _root_.solution {X : ShiftSpace A}
    {hX : X.carrier.Nonempty} {μ : ProbabilityMeasure X.carrier} {K : ℝ}
    (hG : GibbsBounds hX μ K) (hμ : IsInvariant μ)
    {B : Set X.carrier} (hB : MeasurableSet B) (hBinv : (shiftMap X) ⁻¹' B = B)
    {v w : Word A} (hvw : v ++ w ∈ language X) :
    (μ : Measure X.carrier).real (B ∩ cylinder X (v ++ w) 0) *
        (μ : Measure X.carrier).real (cylinder X v 0) ≤
      K ^ 6 * (μ : Measure X.carrier).real (B ∩ cylinder X v 0) *
        (μ : Measure X.carrier).real (cylinder X (v ++ w) 0) := by
  have hu := hG.invariant_inter_prefix_bound hμ hB hBinv v w
  have hl : (μ : Measure X.carrier).real (cylinder X v 0) *
      (μ : Measure X.carrier).real (cylinder X w 0) ≤
      K ^ 3 * (μ : Measure X.carrier).real (cylinder X (v ++ w) 0) := by
    have H := (div_le_iff₀ (pow_pos hG.1 3)).mp (hG.quasiBernoulli hvw).1
    simpa only [mul_comm] using H
  calc
    _ ≤ (K ^ 3 * (μ : Measure X.carrier).real (B ∩ cylinder X v 0) *
          (μ : Measure X.carrier).real (cylinder X w 0)) *
          (μ : Measure X.carrier).real (cylinder X v 0) :=
      mul_le_mul_of_nonneg_right hu measureReal_nonneg
    _ = (K ^ 3 * (μ : Measure X.carrier).real (B ∩ cylinder X v 0)) *
        ((μ : Measure X.carrier).real (cylinder X v 0) *
          (μ : Measure X.carrier).real (cylinder X w 0)) := by ring
    _ ≤ (K ^ 3 * (μ : Measure X.carrier).real (B ∩ cylinder X v 0)) *
        (K ^ 3 * (μ : Measure X.carrier).real (cylinder X (v ++ w) 0)) :=
      mul_le_mul_of_nonneg_left hl (mul_nonneg (pow_nonneg hG.1.le 3) measureReal_nonneg)
    _ = _ := by ring
end GibbsBounds
end BalanceSpecification
