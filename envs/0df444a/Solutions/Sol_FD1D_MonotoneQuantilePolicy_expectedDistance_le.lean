-- Prove2me | solution 1 for FD1D.MonotoneQuantilePolicy.expectedDistance_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:34:08.763346+00:00
-- url     : https://prove2.me/submissions/92f50502-31e6-457f-975a-1b4948e30977

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_MonotoneQuantilePolicy_quantileDistance_eq_cdfTransportArea
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


section
namespace FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace DyadicMass
end DyadicMass
namespace HaarTerm
end HaarTerm
namespace DyadicMass
end DyadicMass
namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
end FiniteLaw
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace DyadicMass
end DyadicMass
namespace MonotoneQuantilePolicy
private theorem selectedDistance_integrable {F : ℝ → ℝ}
    (P : MonotoneQuantilePolicy F) :
    IntegrableOn (fun u => |P.selectedPoint u - u|) (Icc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded (by simp [Real.volume_Icc])
    (P.selected_measurable.sub measurable_id).abs.aestronglyMeasurable (M := 1)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro u hu
  change ‖|P.selectedPoint u - u|‖ ≤ 1
  rw [Real.norm_eq_abs, abs_abs]
  have hs := P.selected_mapsTo hu
  exact abs_le.2 ⟨by linarith [hs.1, hu.2], by linarith [hs.2, hu.1]⟩
private theorem quantileDistance_integrable {F : ℝ → ℝ}
    (P : MonotoneQuantilePolicy F) :
    IntegrableOn (fun u => |P.quantileMap u - u|) (Icc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded (by simp [Real.volume_Icc])
    (P.quantile_measurable.sub measurable_id).abs.aestronglyMeasurable (M := 1)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro u hu
  change ‖|P.quantileMap u - u|‖ ≤ 1
  rw [Real.norm_eq_abs, abs_abs]
  have hq := P.quantile_mapsTo hu
  exact abs_le.2 ⟨by linarith [hq.1, hu.2], by linarith [hq.2, hu.1]⟩
end MonotoneQuantilePolicy
namespace FiniteLaw
end FiniteLaw
end
end FD1D
end

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.MonotoneQuantilePolicy
namespace FD1D.MonotoneQuantilePolicy
theorem _root_.solution {F : ℝ → ℝ} (P : MonotoneQuantilePolicy F)
    : P.expectedDistance ≤ P.withinError +
      cdfTransportArea (fun z => F z - z) := by
  have hrhs : IntegrableOn
      (fun u => P.withinError + |P.quantileMap u - u|) (Icc (0 : ℝ) 1) :=
    (integrableOn_const (C := P.withinError)
      (by simp [Real.volume_Icc])).add P.quantileDistance_integrable
  calc
    P.expectedDistance ≤
        ∫ u in Icc (0 : ℝ) 1, P.withinError + |P.quantileMap u - u| := by
      apply setIntegral_mono_on P.selectedDistance_integrable hrhs measurableSet_Icc
      intro u hu
      calc
        |P.selectedPoint u - u| ≤
            |P.selectedPoint u - P.quantileMap u| +
              |P.quantileMap u - u| := abs_sub_le _ _ _
        _ ≤ P.withinError + |P.quantileMap u - u| :=
          by linarith [P.selected_close u hu]
    _ = P.withinError + P.quantileDistance := by
      rw [MeasureTheory.integral_add
        (integrableOn_const (C := P.withinError)
          (by simp [Real.volume_Icc]))
        P.quantileDistance_integrable]
      simp [quantileDistance, Real.volume_Icc]
    _ = P.withinError + cdfTransportArea (fun z => F z - z) := by
      rw [P.quantileDistance_eq_cdfTransportArea]
end FD1D.MonotoneQuantilePolicy
