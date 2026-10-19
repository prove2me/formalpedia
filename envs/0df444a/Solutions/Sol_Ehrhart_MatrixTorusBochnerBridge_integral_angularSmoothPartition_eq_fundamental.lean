-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.integral_angularSmoothPartition_eq_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/23ec32a6-4203-4e2d-a85c-82141c745ce7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_angularSmoothPartitionBump_zero_of_le
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_angularSmoothPartitionBump_zero_of_ge
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_contDiff_angularSmoothPartition
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_hasCompactSupport_angularSmoothPartition
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_angularSmoothPartition_binary_sum
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_measurableSet_angularFundamentalBox
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_iUnion_binaryAngularFundamentalBox
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_pairwiseDisjoint_binaryAngularFundamentalBox
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_binaryAngularFundamentalBox_eq_translate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerBridge
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerBridge
theorem _root_.solution
    {n : ℕ} {g : Space n → ℂ}
    (hg : Continuous g)
    (hperiod : ∀ (q : Fin n → Bool) (t : Space n),
      g (binaryAngularFundamentalBase q + t) = g t) :
    (∫ t : Space n,
      (angularSmoothPartition t : ℂ) * g t
      ∂(volume : Measure (Space n))) =
    ∫ t : Space n
      in angularFundamentalBox (0 : Space n), g t
      ∂(volume : Measure (Space n)) := by
  classical
  let f : Space n → ℂ :=
    fun t => (angularSmoothPartition t : ℂ) * g t
  have hfc : Continuous f :=
    (Complex.continuous_ofReal.comp
      (contDiff_angularSmoothPartition
        (n := n) (m := 1)).continuous).mul hg
  have hfs : HasCompactSupport f := by
    apply hasCompactSupport_angularSmoothPartition.mono
    intro t ht
    change (angularSmoothPartition t : ℂ) * g t ≠ 0 at ht
    intro hz
    apply ht
    simp [hz]
  have hf : Integrable f
      (volume : Measure (Space n)) :=
    hfc.integrable_of_hasCompactSupport hfs
  let U : Set (Space n) :=
    ⋃ q : Fin n → Bool,
      angularFundamentalBox (binaryAngularFundamentalBase q)
  have houtside : ∀ t : Space n, t ∉ U → f t = 0 := by
    intro t ht
    have hcube :
        t ∉ Set.univ.pi
          (fun _ : Fin n => Set.Ioc (-1 : ℝ) 1) := by
      rw [← iUnion_binaryAngularFundamentalBox n]
      exact ht
    have hnot :
        ¬ ∀ i : Fin n, (-1 : ℝ) < t i ∧ t i ≤ 1 := by
      intro h
      apply hcube
      intro i _
      exact h i
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hbump : angularSmoothPartitionBump (t i) = 0 := by
      by_cases hleft : t i ≤ -1
      · exact angularSmoothPartitionBump_zero_of_le hleft
      · have hright : 1 < t i := by
          by_contra hn
          apply hi
          exact ⟨lt_of_not_ge hleft, le_of_not_gt hn⟩
        exact angularSmoothPartitionBump_zero_of_ge hright.le
    have hzero : angularSmoothPartition t = 0 := by
      unfold angularSmoothPartition
      exact Finset.prod_eq_zero (Finset.mem_univ i) hbump
    simp [f, hzero]
  have htranslate (q : Fin n → Bool) :
      (∫ t : Space n
        in angularFundamentalBox (binaryAngularFundamentalBase q),
        f t ∂(volume : Measure (Space n))) =
      ∫ t : Space n
        in angularFundamentalBox (0 : Space n),
        f (binaryAngularFundamentalBase q + t)
          ∂(volume : Measure (Space n)) := by
    have h :=
      (MeasureTheory.measurePreserving_add_left
        (volume : Measure (Space n))
        (binaryAngularFundamentalBase q)).setIntegral_image_emb
          (measurableEmbedding_addLeft
            (binaryAngularFundamentalBase q))
          f (angularFundamentalBox (0 : Space n))
    rwa [binaryAngularFundamentalBox_eq_translate] at h
  have hshift (q : Fin n → Bool) :
      IntegrableOn
        (fun t : Space n =>
          f (binaryAngularFundamentalBase q + t))
        (angularFundamentalBox (0 : Space n))
        (volume : Measure (Space n)) := by
    have h :=
      (MeasureTheory.measurePreserving_add_left
        (volume : Measure (Space n))
        (binaryAngularFundamentalBase q)).integrable_comp_of_integrable hf
    exact (show Integrable
      (fun t : Space n =>
        f (binaryAngularFundamentalBase q + t))
      (volume : Measure (Space n)) by
        simpa [Function.comp_def] using h).integrableOn
  change (∫ t : Space n, f t
    ∂(volume : Measure (Space n))) = _
  calc
    _ = ∫ t : Space n in U, f t
        ∂(volume : Measure (Space n)) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero houtside).symm
    _ = ∑ q : Fin n → Bool,
      ∫ t : Space n
        in angularFundamentalBox (binaryAngularFundamentalBase q),
        f t ∂(volume : Measure (Space n)) := by
      exact MeasureTheory.integral_iUnion_fintype
        (fun q => measurableSet_angularFundamentalBox
          (binaryAngularFundamentalBase q))
        (pairwiseDisjoint_binaryAngularFundamentalBox n)
        (fun q => hf.integrableOn)
    _ = ∑ q : Fin n → Bool,
      ∫ t : Space n
        in angularFundamentalBox (0 : Space n),
        f (binaryAngularFundamentalBase q + t)
          ∂(volume : Measure (Space n)) := by
      apply Finset.sum_congr rfl
      intro q _
      exact htranslate q
    _ = ∫ t : Space n
        in angularFundamentalBox (0 : Space n),
        ∑ q : Fin n → Bool,
          f (binaryAngularFundamentalBase q + t)
        ∂(volume : Measure (Space n)) := by
      symm
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun q _ => hshift q)
    _ = _ := by
      apply MeasureTheory.setIntegral_congr_fun
        (measurableSet_angularFundamentalBox
          (0 : Space n))
      intro t ht
      have ht0 : ∀ i : Fin n, 0 ≤ t i := by
        intro i
        have h := ht i
        have h' : 0 < t i ∧ t i ≤ (1 : ℝ) := by
          simpa using h
        exact h'.1.le
      have ht1 : ∀ i : Fin n, t i ≤ 1 := by
        intro i
        have h := ht i
        have h' : 0 < t i ∧ t i ≤ (1 : ℝ) := by
          simpa using h
        exact h'.2
      have hsum :
          (∑ q : Fin n → Bool,
            angularSmoothPartition
              (binaryAngularFundamentalBase q + t)) = 1 := by
        calc
          _ = ∑ q : Fin n → Bool,
            angularSmoothPartition
              (fun i => t i - if q i then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro q _
            congr 1
            funext i
            simp only [Pi.add_apply,
              binaryAngularFundamentalBase]
            split <;> ring
          _ = 1 := angularSmoothPartition_binary_sum t ht0 ht1
      have hcomplex :
          (∑ q : Fin n → Bool,
            (angularSmoothPartition
              (binaryAngularFundamentalBase q + t) : ℂ)) = 1 := by
        exact_mod_cast hsum
      change
        (∑ q : Fin n → Bool,
          (angularSmoothPartition
            (binaryAngularFundamentalBase q + t) : ℂ) *
            g (binaryAngularFundamentalBase q + t)) = g t
      simp_rw [hperiod]
      rw [← Finset.sum_mul, hcomplex, one_mul]
end Ehrhart.MatrixTorusBochnerBridge
