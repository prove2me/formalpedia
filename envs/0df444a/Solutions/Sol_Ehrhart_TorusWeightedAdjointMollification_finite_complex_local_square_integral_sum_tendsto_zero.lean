-- Prove2me | solution 1 for Ehrhart.TorusWeightedAdjointMollification.finite_complex_local_square_integral_sum_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/2a2675d5-c071-47aa-a153-ba57143c6574

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusWeightedAdjointMollification_complex_norm_add_sq_le_two_mul_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeightedAdjointMollification
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity WeightedTorusDolbeault TorusWeakDolbeaultMollification
open TorusFriedrichsMollifierEstimates TorusMollifiedBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusWeightedAdjointMollification
theorem _root_.solution
    {n : ℕ} {ι : Type*}
    (s : Finset ι)
    (g : ι → ℕ → LogSpace n → ℂ)
    {K : Set (LogSpace n)} (hK : IsCompact K)
    (hcontinuous : ∀ i ∈ s, ∀ k : ℕ, Continuous (g i k))
    (hvanish : ∀ i ∈ s,
      Tendsto
        (fun k : ℕ =>
          ∫ x in K, ‖g i k x‖ ^ 2
            ∂(volume : Measure (LogSpace n)))
        atTop (nhds 0)) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K, ‖∑ i ∈ s, g i k x‖ ^ 2
          ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hice : ∀ k : ℕ, Continuous (g i k) :=
      fun k => hcontinuous i (Finset.mem_insert_self i s) k
    have hsce : ∀ j ∈ s, ∀ k : ℕ, Continuous (g j k) := by
      intro j hj k
      exact hcontinuous j (Finset.mem_insert_of_mem hj) k
    have hival :
        Tendsto
          (fun k : ℕ =>
            ∫ x in K, ‖g i k x‖ ^ 2
              ∂(volume : Measure (LogSpace n)))
          atTop (nhds 0) :=
      hvanish i (Finset.mem_insert_self i s)
    have hsval : ∀ j ∈ s,
        Tendsto
          (fun k : ℕ =>
            ∫ x in K, ‖g j k x‖ ^ 2
              ∂(volume : Measure (LogSpace n)))
          atTop (nhds 0) := by
      intro j hj
      exact hvanish j (Finset.mem_insert_of_mem hj)
    have hrest := ih hsce hsval
    have hbound (k : ℕ) :
        (∫ x in K, ‖∑ j ∈ insert i s, g j k x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) ≤
        2 *
          ((∫ x in K, ‖g i k x‖ ^ 2
              ∂(volume : Measure (LogSpace n))) +
           (∫ x in K, ‖∑ j ∈ s, g j k x‖ ^ 2
              ∂(volume : Measure (LogSpace n)))) := by
      have hci : Continuous (fun x : LogSpace n => ‖g i k x‖ ^ 2) :=
        (hice k).norm.pow 2
      have hcs : Continuous
          (fun x : LogSpace n => ‖∑ j ∈ s, g j k x‖ ^ 2) :=
        (continuous_finsetSum s (fun j hj => hsce j hj k)).norm.pow 2
      have hinti : IntegrableOn
          (fun x : LogSpace n => ‖g i k x‖ ^ 2) K
          (volume : Measure (LogSpace n)) :=
        hci.locallyIntegrable.integrableOn_isCompact hK
      have hints : IntegrableOn
          (fun x : LogSpace n => ‖∑ j ∈ s, g j k x‖ ^ 2) K
          (volume : Measure (LogSpace n)) :=
        hcs.locallyIntegrable.integrableOn_isCompact hK
      have hintadd : IntegrableOn
          (fun x : LogSpace n =>
            2 * (‖g i k x‖ ^ 2 + ‖∑ j ∈ s, g j k x‖ ^ 2)) K
          (volume : Measure (LogSpace n)) :=
        (hinti.add hints).const_mul (2 : ℝ)
      have hcadd : Continuous
          (fun x : LogSpace n =>
            ‖g i k x + ∑ j ∈ s, g j k x‖ ^ 2) :=
        ((hice k).add
          (continuous_finsetSum s
            (fun j hj => hsce j hj k))).norm.pow 2
      have hintleft : IntegrableOn
          (fun x : LogSpace n =>
            ‖g i k x + ∑ j ∈ s, g j k x‖ ^ 2) K
          (volume : Measure (LogSpace n)) :=
        hcadd.locallyIntegrable.integrableOn_isCompact hK
      calc
        (∫ x in K, ‖∑ j ∈ insert i s, g j k x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) =
          ∫ x in K, ‖g i k x + ∑ j ∈ s, g j k x‖ ^ 2
            ∂(volume : Measure (LogSpace n)) := by
              simp [Finset.sum_insert, hi]
        _ ≤ ∫ x in K,
              2 * (‖g i k x‖ ^ 2 + ‖∑ j ∈ s, g j k x‖ ^ 2)
              ∂(volume : Measure (LogSpace n)) := by
          apply MeasureTheory.setIntegral_mono
          · exact hintleft
          · exact hintadd
          · intro x
            exact complex_norm_add_sq_le_two_mul_add
              (g i k x) (∑ j ∈ s, g j k x)
        _ = 2 *
          ((∫ x in K, ‖g i k x‖ ^ 2
              ∂(volume : Measure (LogSpace n))) +
           (∫ x in K, ‖∑ j ∈ s, g j k x‖ ^ 2
              ∂(volume : Measure (LogSpace n)))) := by
          rw [integral_const_mul, integral_add hinti hints]
    have hupper :
        Tendsto
          (fun k : ℕ =>
            2 *
              ((∫ x in K, ‖g i k x‖ ^ 2
                  ∂(volume : Measure (LogSpace n))) +
               (∫ x in K, ‖∑ j ∈ s, g j k x‖ ^ 2
                  ∂(volume : Measure (LogSpace n)))))
          atTop (nhds 0) := by
      convert (hival.add hrest).const_mul (2 : ℝ) using 1 ; norm_num
    exact squeeze_zero
      (fun k => integral_nonneg (fun x => sq_nonneg _))
      hbound hupper
end Ehrhart.TorusWeightedAdjointMollification
