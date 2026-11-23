-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NthRootMeasurability.densityChange_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:18.656133+00:00
-- url     : https://prove2.me/submissions/c74294c6-5713-42cb-931b-ec5903875e71

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_real_id

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
theorem _root_.solution : DensityChange := by
  intro s M t g hs hM ht hg
  have hs0 : s ≠ 0 := by omega
  have hu : ((-1 : ℂ) ^ (s + 1) * t ^ (s - 1)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ht)
  calc _ = ∫⁻ c, ((nthRoots s (((-1 : ℂ) ^ (s + 1) * t ^ (s - 1)) * c)).map
            (fun z => ENNReal.ofReal (‖t‖ ^ (2 * (s - 1) * (M + s - 2)) *
              ‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * z ^ s‖ ^ (2 * (M - 2)) /
                (‖t‖ ^ (2 * (s - 1) ^ 2) * (s : ℝ) ^ 2)) *
              (ENNReal.ofReal (‖z‖ ^ (2 * (s - 1) ^ 2)) * g z))).sum := by
        refine lintegral_congr (fun c => ?_)
        rw [show (-1 : ℂ) ^ (s + 1) * (c * t ^ (s - 1)) = ((-1 : ℂ) ^ (s + 1) * t ^ (s - 1)) * c by
          ring, ← Multiset.sum_map_mul_left]
        congr 1
        refine Multiset.map_congr rfl (fun z hz => ?_)
        rw [mem_nthRoots (by omega)] at hz
        rw [hz, inv_mul_cancel_left₀ hu]
    _ = ∫⁻ z, ENNReal.ofReal (‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * (s * z ^ (s - 1))‖ ^ 2) *
            (ENNReal.ofReal (‖t‖ ^ (2 * (s - 1) * (M + s - 2)) *
              ‖((-1 : ℂ) ^ (s + 1) * t ^ (s - 1))⁻¹ * z ^ s‖ ^ (2 * (M - 2)) /
                (‖t‖ ^ (2 * (s - 1) ^ 2) * (s : ℝ) ^ 2)) *
              (ENNReal.ofReal (‖z‖ ^ (2 * (s - 1) ^ 2)) * g z)) :=
        core s hs0 _ hu _ (by
          refine (Measurable.ennreal_ofReal (by fun_prop)).mul
            ((Measurable.ennreal_ofReal (by fun_prop)).mul hg))
    _ = _ := by
        refine lintegral_congr_ae ?_
        filter_upwards [Measure.ae_ne volume (0 : ℂ)] with z hz
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), real_id s M hs hM t z ht hz]
end Formalism.FourierDecayAlt.P.NthRootMeasurability
