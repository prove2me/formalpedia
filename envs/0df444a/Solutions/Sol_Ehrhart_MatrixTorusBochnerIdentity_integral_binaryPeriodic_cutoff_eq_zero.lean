-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.integral_binaryPeriodic_cutoff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/e02b8950-2938-4e91-b9f1-d72e26c0e328

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
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
open Ehrhart.MatrixTorusBochnerIdentity
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerIdentity
theorem _root_.solution
    {n : ℕ} {κ : Space n → ℝ}
    (hκ : Continuous κ)
    (hκcompact : HasCompactSupport κ)
    (houtside : ∀ t : Space n,
      t ∉ Set.univ.pi
        (fun _ : Fin n => Set.Ioc (-1 : ℝ) 1) → κ t = 0)
    (hcancel : ∀ t : Space n,
      (∀ i : Fin n, 0 ≤ t i) →
      (∀ i : Fin n, t i ≤ 1) →
      (∑ q : Fin n → Bool,
        κ (binaryAngularFundamentalBase q + t)) = 0)
    {g : Space n → ℂ}
    (hg : Continuous g)
    (hperiod : ∀ (q : Fin n → Bool) (t : Space n),
      g (binaryAngularFundamentalBase q + t) = g t) :
    (∫ t : Space n,
      (κ t : ℂ) * g t
      ∂(volume : Measure (Space n))) = 0 := by
  classical
  let F : Space n → ℂ :=
    fun t => (κ t : ℂ) * g t
  have hFc : Continuous F :=
    (Complex.continuous_ofReal.comp hκ).mul hg
  have hFs : HasCompactSupport F := by
    apply hκcompact.mono
    intro t ht
    change (κ t : ℂ) * g t ≠ 0 at ht
    intro hz
    exact ht (by simp [hz])
  have hF : Integrable F
      (volume : Measure (Space n)) :=
    hFc.integrable_of_hasCompactSupport hFs
  let U : Set (Space n) :=
    ⋃ q : Fin n → Bool,
      angularFundamentalBox (binaryAngularFundamentalBase q)
  have hvanish : ∀ t : Space n, t ∉ U → F t = 0 := by
    intro t ht
    have hcube :
        t ∉ Set.univ.pi
          (fun _ : Fin n => Set.Ioc (-1 : ℝ) 1) := by
      rw [← iUnion_binaryAngularFundamentalBox n]
      exact ht
    simp [F, houtside t hcube]
  have htranslate (q : Fin n → Bool) :
      (∫ t : Space n
        in angularFundamentalBox (binaryAngularFundamentalBase q),
        F t ∂(volume : Measure (Space n))) =
      ∫ t : Space n
        in angularFundamentalBox (0 : Space n),
        F (binaryAngularFundamentalBase q + t)
          ∂(volume : Measure (Space n)) := by
    have h :=
      (MeasureTheory.measurePreserving_add_left
        (volume : Measure (Space n))
        (binaryAngularFundamentalBase q)).setIntegral_image_emb
          (measurableEmbedding_addLeft
            (binaryAngularFundamentalBase q))
          F (angularFundamentalBox (0 : Space n))
    rwa [binaryAngularFundamentalBox_eq_translate] at h
  have hshift (q : Fin n → Bool) :
      IntegrableOn
        (fun t : Space n =>
          F (binaryAngularFundamentalBase q + t))
        (angularFundamentalBox (0 : Space n))
        (volume : Measure (Space n)) := by
    have h :=
      (MeasureTheory.measurePreserving_add_left
        (volume : Measure (Space n))
        (binaryAngularFundamentalBase q)).integrable_comp_of_integrable hF
    exact (show Integrable
      (fun t : Space n =>
        F (binaryAngularFundamentalBase q + t))
      (volume : Measure (Space n)) by
        simpa [Function.comp_def] using h).integrableOn
  change (∫ t : Space n, F t
    ∂(volume : Measure (Space n))) = 0
  calc
    _ = ∫ t : Space n in U, F t
        ∂(volume : Measure (Space n)) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hvanish).symm
    _ = ∑ q : Fin n → Bool,
      ∫ t : Space n
        in angularFundamentalBox (binaryAngularFundamentalBase q),
        F t ∂(volume : Measure (Space n)) := by
      exact MeasureTheory.integral_iUnion_fintype
        (fun q => measurableSet_angularFundamentalBox
          (binaryAngularFundamentalBase q))
        (pairwiseDisjoint_binaryAngularFundamentalBox n)
        (fun _ => hF.integrableOn)
    _ = ∑ q : Fin n → Bool,
      ∫ t : Space n
        in angularFundamentalBox (0 : Space n),
        F (binaryAngularFundamentalBase q + t)
          ∂(volume : Measure (Space n)) := by
      apply Finset.sum_congr rfl
      intro q _
      exact htranslate q
    _ = ∫ t : Space n
        in angularFundamentalBox (0 : Space n),
        ∑ q : Fin n → Bool,
          F (binaryAngularFundamentalBase q + t)
        ∂(volume : Measure (Space n)) := by
      symm
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun q _ => hshift q)
    _ = ∫ _t : Space n
        in angularFundamentalBox (0 : Space n),
        (0 : ℂ) ∂(volume : Measure (Space n)) := by
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
      have hreal :
          (∑ q : Fin n → Bool,
            κ (binaryAngularFundamentalBase q + t)) = 0 :=
        hcancel t ht0 ht1
      have hcomplex :
          (∑ q : Fin n → Bool,
            (κ (binaryAngularFundamentalBase q + t) : ℂ)) = 0 := by
        exact_mod_cast hreal
      change
        (∑ q : Fin n → Bool,
          (κ (binaryAngularFundamentalBase q + t) : ℂ) *
            g (binaryAngularFundamentalBase q + t)) = 0
      simp_rw [hperiod]
      rw [← Finset.sum_mul, hcomplex, zero_mul]
    _ = 0 := by simp
end Ehrhart.MatrixTorusBochnerIdentity
