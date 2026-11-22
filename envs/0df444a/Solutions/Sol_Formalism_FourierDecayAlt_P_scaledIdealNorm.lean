-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.scaledIdealNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:19:15.074163+00:00
-- url     : https://prove2.me/submissions/24b947c3-f035-4971-ba6b-c3e33d92eb31

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Theorems.Thm_Formalism_FourierDecayAlt_P_degreeFacts_statement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x1
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.NormIdl := by
  intro E _ _ _ g k ν hg
  have hdeg := degreeFacts_statement E
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hD0 : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
  have hrd : 0 < rd E := by
    unfold rd
    apply Real.rpow_pos_of_pos
    have : (0 : ℤ) < |discr E| := abs_pos.2 (discr_ne_zero E)
    exact_mod_cast this
  have hD : ((|discr E| : ℤ) : ℝ) = rd E ^ (2 * deg E) := by
    unfold rd
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0, hdeg.1]
    have : ((2 * deg E : ℕ) : ℝ) ≠ 0 := by
      have := hdeg.2.2
      positivity
    rw [inv_mul_cancel₀ this, Real.rpow_one]
  have h1 : FractionalIdeal.absNorm (dd E) = ((|discr E| : ℤ) : ℚ) := by
    unfold dd
    rw [FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E, Nat.cast_natAbs]
  have h2 : FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ k))
      = ((g : ℚ) ^ (2 * deg E)) ^ k := by
    rw [FractionalIdeal.absNorm_span_singleton,
      show (g : E) ^ k = algebraMap ℚ E ((g : ℚ) ^ k) by rw [map_zpow₀, map_natCast],
      Algebra.norm_algebraMap, hdeg.1, abs_of_nonneg (by positivity)]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  unfold idl
  rw [map_mul, map_zpow₀, h1, h2]
  push_cast
  have hD' : (|(discr E : ℝ)|) = rd E ^ (2 * deg E) := by rw [← hD]; push_cast; rfl
  rw [hD']
  have : (rd E ^ (2 * deg E)) ^ ν * ((g : ℝ) ^ (2 * deg E)) ^ k
      = (((g : ℝ) ^ k * rd E ^ ν) ^ deg E) ^ 2 := by
    rw [← zpow_natCast (rd E), ← zpow_natCast (g : ℝ), ← zpow_mul, ← zpow_mul, ← pow_mul, mul_pow,
      ← zpow_natCast (((g : ℝ) ^ k)), ← zpow_natCast ((rd E ^ ν)), ← zpow_mul, ← zpow_mul, mul_comm]
    congr 2 <;> (push_cast; ring)
  rw [this, Real.sqrt_sq (by positivity)]
end Formalism.FourierDecayAlt.P
