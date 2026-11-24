-- Prove2me | solution 1 for BalanceSpecification.invariant_inter_cylinder_real_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:07:25.904714+00:00
-- url     : https://prove2.me/submissions/06af0f11-c5fe-45b5-8dab-3f22b30770ff

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_cylinder_preimage_iterate
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
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
theorem _root_.solution {X : ShiftSpace A}
    {μ : ProbabilityMeasure X.carrier} (hμ : IsInvariant μ)
    {B : Set X.carrier} (hB : MeasurableSet B)
    (hBinv : (shiftMap X) ⁻¹' B = B) (w : Word A) (k : ℤ) :
    (μ : Measure X.carrier).real (B ∩ cylinder X w k) =
      (μ : Measure X.carrier).real (B ∩ cylinder X w 0) := by
  have hiter (n : ℕ) : (shiftMap X)^[n] ⁻¹' B = B :=
    Function.IsFixedPt.preimage_iterate hBinv n
  have hnat (l : ℤ) (n : ℕ) :
      (μ : Measure X.carrier).real (B ∩ cylinder X w ((n : ℤ) + l)) =
        (μ : Measure X.carrier).real (B ∩ cylinder X w l) := by
    have H := (hμ.iterate n).measureReal_preimage
      (hB.inter (measurableSet_cylinder X w l)).nullMeasurableSet
    simpa only [Set.preimage_inter, hiter, cylinder_preimage_iterate] using H
  cases k with
  | ofNat n => simpa only [add_zero, Int.ofNat_eq_natCast] using hnat 0 n
  | negSucc n =>
    have H := hnat (Int.negSucc n) (n + 1)
    have hk : ((n + 1 : ℕ) : ℤ) + Int.negSucc n = 0 := by omega
    rw [hk] at H
    exact H.symm
end BalanceSpecification
