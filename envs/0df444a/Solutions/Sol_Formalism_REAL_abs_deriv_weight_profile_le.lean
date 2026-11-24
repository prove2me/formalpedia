-- Prove2me | solution 1 for Formalism.REAL.abs_deriv_weight_profile_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:01:33.086446+00:00
-- url     : https://prove2.me/submissions/759b7a5d-748c-499f-aa7a-007de35f1c7e

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasComm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IntegrableComplexContinuousBoundedSupport
import Theorems.Thm_Formalism_REAL_cutoff_profile_eq_one
import Theorems.Thm_Formalism_REAL_cutoff_profile_le_one
import Theorems.Thm_Formalism_REAL_cutoffDerivBound_nonneg
import Theorems.Thm_Formalism_REAL_hasDerivAt_cutoff_alt
import Theorems.Thm_Formalism_REAL_abs_deriv_cutoff_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ENNReal
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution {a R : ℝ} (ha : 0 ≤ a) (hR : 1 ≤ R) (t : ℝ) :
    |deriv (weightProfileAlt a R) t| ≤ radialCutoff R t * Real.exp (2 * a * t) * (2 * cutoffDerivBound + 2 * a) := by
  have hR0 : 0 < R := by linarith
  have hc := hasDerivAt_cutoff_alt R t
  have he : HasDerivAt (fun s => Real.exp (2 * a * s)) (Real.exp (2 * a * t) * (2 * a)) t := by
    have := ((hasDerivAt_id t).const_mul (2 * a)).exp
    simpa using this
  have hd : HasDerivAt (weightProfileAlt a R)
      ((2 : ℕ) * radialCutoff R t ^ (2 - 1) * (deriv cutoffProfile (t / R) * (1 / R)) * Real.exp (2 * a * t) +
        radialCutoff R t ^ 2 * (Real.exp (2 * a * t) * (2 * a))) t :=
    (hc.pow 2).mul he
  rw [hd.deriv]
  have hχ0 : 0 ≤ radialCutoff R t := cutoff_profile_eq_one _
  have hχ1 : radialCutoff R t ≤ 1 := cutoff_profile_le_one _
  have hE : 0 < Real.exp (2 * a * t) := Real.exp_pos _
  have hd' : |deriv cutoffProfile (t / R) * (1 / R)| ≤ cutoffDerivBound := by
    have h1 := abs_deriv_cutoff_le hR0 t
    rw [(hasDerivAt_cutoff_alt R t).deriv] at h1
    refine h1.trans ?_
    rw [div_le_iff₀ hR0]
    nlinarith [cutoffDerivBound_nonneg]
  have hsq : radialCutoff R t ^ 2 ≤ radialCutoff R t := by nlinarith
  push_cast
  simp only [pow_one]
  calc |2 * radialCutoff R t * (deriv cutoffProfile (t / R) * (1 / R)) * Real.exp (2 * a * t) +
        radialCutoff R t ^ 2 * (Real.exp (2 * a * t) * (2 * a))|
      ≤ |2 * radialCutoff R t * (deriv cutoffProfile (t / R) * (1 / R)) * Real.exp (2 * a * t)| +
        |radialCutoff R t ^ 2 * (Real.exp (2 * a * t) * (2 * a))| := abs_add_le _ _
    _ = 2 * radialCutoff R t * |deriv cutoffProfile (t / R) * (1 / R)| * Real.exp (2 * a * t) +
        radialCutoff R t ^ 2 * (Real.exp (2 * a * t) * (2 * a)) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hχ0, abs_of_pos hE,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ radialCutoff R t ^ 2 * (Real.exp (2 * a * t) * (2 * a)))]
        norm_num
    _ ≤ 2 * radialCutoff R t * cutoffDerivBound * Real.exp (2 * a * t) +
        radialCutoff R t * (Real.exp (2 * a * t) * (2 * a)) := by
        gcongr
    _ = radialCutoff R t * Real.exp (2 * a * t) * (2 * cutoffDerivBound + 2 * a) := by ring
end Formalism.REAL
