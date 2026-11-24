-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.perron_integrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:00:24.902713+00:00
-- url     : https://prove2.me/submissions/e774a78a-74e6-4675-b9b6-d2d206719d91

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_neg_log_deriv_le_tsum
import Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_integrand_continuous
import Theorems.Thm_Formalism_ZF_perron_denom_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Integrable (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) := by
  set B := ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ with hBdef
  have hB : 0 ≤ B := tsum_nonneg (fun n => norm_nonneg _)
  set dd := min ((σ₀ - 1) ^ 2) 1 with hdddef
  have hdd : 0 < dd := lt_min (by nlinarith) one_pos
  have hy' : 0 < y ^ σ₀ := Real.rpow_pos_of_pos hy _
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (B * y ^ σ₀ / dd))
    (perron_integrand_continuous χ hy hσ).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hre : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp
  unfold Fchi
  rw [norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hy, hre]
  have hL := norm_neg_log_deriv_le_tsum χ hσ _ hre
  have hD := Formalism.ZF.perron_denom_bound hσ t
  have hpos : 0 < dd * (1 + t ^ 2) := by positivity
  have hc : 0 ≤ B * y ^ σ₀ / dd * (1 + t ^ 2)⁻¹ :=
    mul_nonneg (div_nonneg (mul_nonneg hB hy'.le) hdd.le) (inv_nonneg.mpr (by positivity))
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hD)]
  calc ‖negLD χ ((σ₀ : ℂ) + t * I)‖ * y ^ σ₀ ≤ B * y ^ σ₀ :=
        mul_le_mul_of_nonneg_right hL hy'.le
    _ = B * y ^ σ₀ / dd * (1 + t ^ 2)⁻¹ * (dd * (1 + t ^ 2)) := by
        field_simp
    _ ≤ B * y ^ σ₀ / dd * (1 + t ^ 2)⁻¹ * ‖((σ₀ : ℂ) + t * I) * ((σ₀ : ℂ) + t * I - 1)‖ :=
        mul_le_mul_of_nonneg_left hD hc
end Formalism.ZeroFreeDirichlet
