-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiscFubiniVolume.disc_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:17:02.732106+00:00
-- url     : https://prove2.me/submissions/8f2cb654-0f98-42fb-a389-e606b778ec7f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscMeanValue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Metric
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiscFubiniVolume
namespace Formalism.FourierDecayAlt.P.DiscFubiniVolume
theorem _root_.solution {R ρ : ℝ} (hR : 0 < R) :
    ∫ t in (-R)..R, ((2 * Real.sqrt (R ^ 2 - t ^ 2) : ℝ) : ℂ) * ee ρ t =
      ((2 * R ^ 2 : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (g0 s : ℂ) * ee (ρ * R) s := by
  have hR0 : R ≠ 0 := hR.ne'
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR0
  have hsq : ∀ s : ℝ, Real.sqrt (1 - s ^ 2) = Real.sqrt (R ^ 2 - (R * s) ^ 2) / R := by
    intro s
    rw [show R ^ 2 - (R * s) ^ 2 = R ^ 2 * (1 - s ^ 2) by ring, Real.sqrt_mul (sq_nonneg R),
      Real.sqrt_sq hR.le, mul_div_cancel_left₀ _ hR0]
  have hee : ∀ s : ℝ, ee (ρ * R) s = ee ρ (R * s) := by
    intro s
    simp only [ee]
    congr 2
    push_cast
    ring
  have key : (fun s : ℝ => (g0 s : ℂ) * ee (ρ * R) s) =
      fun s => ((Real.sqrt (R ^ 2 - (R * s) ^ 2) / R : ℝ) : ℂ) * ee ρ (R * s) := by
    funext s
    rw [hee, show g0 s = Real.sqrt (1 - s ^ 2) from rfl, hsq]
  have hint : (∫ s in (-1 : ℝ)..1, (g0 s : ℂ) * ee (ρ * R) s) =
      ∫ s in (-1 : ℝ)..1, ((Real.sqrt (R ^ 2 - (R * s) ^ 2) / R : ℝ) : ℂ) * ee ρ (R * s) := by
    rw [key]
  have hcomp := intervalIntegral.integral_comp_mul_left (a := (-1 : ℝ)) (b := 1)
    (fun t : ℝ => ((Real.sqrt (R ^ 2 - t ^ 2) / R : ℝ) : ℂ) * ee ρ t) hR0
  rw [hint, hcomp, mul_neg, mul_one, Complex.real_smul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  push_cast
  field_simp
end Formalism.FourierDecayAlt.P.DiscFubiniVolume
