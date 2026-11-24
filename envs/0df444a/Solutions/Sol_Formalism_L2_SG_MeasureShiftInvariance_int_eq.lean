-- Prove2me | solution 1 for Formalism.L2.SG.MeasureShiftInvariance.int_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:36:40.059603+00:00
-- url     : https://prove2.me/submissions/9186b8c0-f5a9-4e6e-b082-492bc94025fe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_lint_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
namespace Formalism.L2.SG.MeasureShiftInvariance
section SF
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable (h : G)
end SF
section Unfold
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure G) [SFinite ν]
end Unfold
section Boch
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure G) [SFinite ν]
private theorem ennreal_eq_of_mul_left_eq {c a b : ℝ≥0∞} (h0 : c ≠ 0) (ht : c ≠ ⊤) (h : c * a = c * b) : a = b := by
  first
  | exact (ENNReal.mul_right_inj h0 ht).1 h
  | (calc a = c⁻¹ * (c * a) := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
      _ = c⁻¹ * (c * b) := by rw [h]
      _ = b := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul])
private theorem setIntegral_eq_of_fiber_measure_eq {A B : Set G} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hcB : ∀ x, ν {r | r * x ∈ B} = c) (hcA : ∀ y, ν {r | r⁻¹ * y ∈ A} = c)
    (f : G → ℝ) (hf : AEStronglyMeasurable f μ) (hinv : ∀ᵐ r ∂ν, ∀ x, f (r⁻¹ * x) = f x)
    (hfA : IntegrableOn f A μ) (hfB : IntegrableOn f B μ) :
    ∫ x in A, f x ∂μ = ∫ x in B, f x ∂μ := by
  have e1 := lint_eq (μ := μ) ν hA hB c hcB hcA
    (fun x => ENNReal.ofReal (f x)) hf.aemeasurable.ennreal_ofReal
    (by filter_upwards [hinv] with r hr x; simp only [hr])
  have e2 := lint_eq (μ := μ) ν hA hB c hcB hcA
    (fun x => ENNReal.ofReal (-f x)) hf.aemeasurable.neg.ennreal_ofReal
    (by filter_upwards [hinv] with r hr x; simp only [hr])
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfA,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfB,
    ennreal_eq_of_mul_left_eq hc0 hct e1, ennreal_eq_of_mul_left_eq hc0 hct e2]
end Boch
section Shift
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
end Shift
section ShiftG
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
end ShiftG
end Formalism.L2.SG.MeasureShiftInvariance
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.MeasureShiftInvariance
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure G) [SFinite ν]
namespace Formalism.L2.SG.MeasureShiftInvariance
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {A B : Set G}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hcB : ∀ x, ν {r | r * x ∈ B} = c) (hcA : ∀ y, ν {r | r⁻¹ * y ∈ A} = c)
    (f : G → E) (hf : AEStronglyMeasurable f μ) (hinv : ∀ᵐ r ∂ν, ∀ x, f (r⁻¹ * x) = f x)
    (hfA : IntegrableOn f A μ) : ∫ x in A, f x ∂μ = ∫ x in B, f x ∂μ := by
  have hfB : IntegrableOn f B μ := by
    have hg : AEMeasurable (fun x => ‖f x‖ₑ) μ := by
      first
      | exact hf.enorm
      | exact (continuous_enorm.comp_aestronglyMeasurable hf).aemeasurable
    have e := lint_eq (μ := μ) ν hA hB c hcB hcA
      (fun x => ‖f x‖ₑ) hg (by filter_upwards [hinv] with r hr x; simp only [hr])
    have e' := ennreal_eq_of_mul_left_eq hc0 hct e
    have hA' : ∫⁻ x in A, ‖f x‖ₑ ∂μ < ⊤ := by
      first
      | exact hfA.2
      | exact hfA.hasFiniteIntegral
      | exact hasFiniteIntegral_iff_enorm.1 hfA.2
    refine ⟨hf.restrict, ?_⟩
    first
    | (show ∫⁻ x in B, ‖f x‖ₑ ∂μ < ⊤; rw [← e']; exact hA')
    | (rw [hasFiniteIntegral_iff_enorm, ← e']; exact hA')
  have key : ∀ L : E →L[ℝ] ℝ, L (∫ x in A, f x ∂μ) = L (∫ x in B, f x ∂μ) := by
    intro L
    rw [← L.integral_comp_comm hfA, ← L.integral_comp_comm hfB]
    exact setIntegral_eq_of_fiber_measure_eq (μ := μ) ν hA hB c hc0 hct hcB hcA (fun x => L (f x))
      (L.continuous.comp_aestronglyMeasurable hf)
      (by filter_upwards [hinv] with r hr x; simp only [hr])
      (L.integrable_comp hfA) (L.integrable_comp hfB)
  by_contra hne
  first
  | (obtain ⟨L, hL⟩ : ∃ L : E →L[ℝ] ℝ, L (∫ x in A, f x ∂μ) ≠ L (∫ x in B, f x ∂μ) :=
        SeparatingDual.exists_separating_of_ne hne
     exact hL (key L))
  | exact hne ((NormedSpace.eq_iff_forall_dual_eq ℝ).2 key)
end Formalism.L2.SG.MeasureShiftInvariance
