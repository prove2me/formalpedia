-- Prove2me | solution 1 for BalanceSpecification.IsInvariant.cylinder_real_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:07:25.482917+00:00
-- url     : https://prove2.me/submissions/9de433e3-ba23-47e3-aaa3-d55bbcc8a88f

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Measures
public import Theorems.Thm_BalanceSpecification_cylinder_preimage_iterate
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
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
open MeasureTheory
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
namespace IsInvariant
theorem _root_.solution {X : ShiftSpace A}
    {μ : ProbabilityMeasure X.carrier} (hμ : IsInvariant μ) (w : Word A) (k : ℤ) :
    (μ : Measure X.carrier).real (cylinder X w k) =
      (μ : Measure X.carrier).real (cylinder X w 0) := by
  have hnat (l : ℤ) (n : ℕ) :
      (μ : Measure X.carrier).real (cylinder X w ((n : ℤ) + l)) =
        (μ : Measure X.carrier).real (cylinder X w l) := by
    have H := (hμ.iterate n).measureReal_preimage
      (measurableSet_cylinder X w l).nullMeasurableSet
    simpa only [cylinder_preimage_iterate] using H
  cases k with
  | ofNat n => simpa only [add_zero, Int.ofNat_eq_natCast] using hnat 0 n
  | negSucc n =>
    have H := hnat (Int.negSucc n) (n + 1)
    have hk : ((n + 1 : ℕ) : ℤ) + Int.negSucc n = 0 := by omega
    rw [hk] at H
    exact H.symm
end IsInvariant
end BalanceSpecification
