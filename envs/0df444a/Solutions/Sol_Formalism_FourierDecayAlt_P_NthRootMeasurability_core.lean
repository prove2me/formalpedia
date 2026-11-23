-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NthRootMeasurability.core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:36.468494+00:00
-- url     : https://prove2.me/submissions/1e4645f0-b694-4faa-b6f6-917d3074d49c

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_detC
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_measurable_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_measurableSet_A
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_sum_roots
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_A_disjoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_A_union
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_image_A
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_injOn_A

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NthRootMeasurability
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.NthRootMeasurability
theorem _root_.solution (s : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) (H : ℂ → ENNReal) (hH : Measurable H) :
    ∫⁻ c, ((nthRoots s (u * c)).map H).sum =
      ∫⁻ z, ENNReal.ofReal (‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2) * H z := by
  simp_rw [sum_roots s hs H]
  rw [lintegral_finsetSum (Finset.range s) (f := fun k c => H (R s k (u * c)))
    (fun k _ => hH.comp ((measurable_R s k).comp (measurable_const_mul u)))]
  have step : ∀ k, ∫⁻ c, H (R s k (u * c)) =
      ∫⁻ z in A s k, ENNReal.ofReal (‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2) * H z := by
    intro k
    calc ∫⁻ c, H (R s k (u * c)) = ∫⁻ c in {0}ᶜ, H (R s k (u * c)) := by
          rw [MeasureTheory.restrict_compl_singleton]
      _ = ∫⁻ c in (fun z => u⁻¹ * z ^ s) '' A s k, H (R s k (u * c)) := by
          rw [image_A s k hs u hu]
      _ = ∫⁻ z in A s k, ENNReal.ofReal |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
            (u⁻¹ * (s * z ^ (s - 1)))).restrictScalars ℝ).det| *
            H (R s k (u * (u⁻¹ * z ^ s))) :=
          lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (measurableSet_A s k)
            (fun z _ => (((hasDerivAt_pow s z).const_mul u⁻¹).hasFDerivAt.restrictScalars
              ℝ).hasFDerivWithinAt) (injOn_A s k u hu) _
      _ = _ := by
          refine setLIntegral_congr_fun (measurableSet_A s k) (fun z hz => ?_)
          rw [detC, abs_of_nonneg (sq_nonneg _), ← mul_assoc (u) u⁻¹, mul_inv_cancel₀ hu, one_mul,
            hz.2]
  simp_rw [step]
  rw [← lintegral_biUnion_finset (A_disjoint s hs) (fun k _ => measurableSet_A s k), A_union s hs,
    MeasureTheory.restrict_compl_singleton]
end Formalism.FourierDecayAlt.P.NthRootMeasurability
