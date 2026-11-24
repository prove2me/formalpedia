-- Prove2me | solution 1 for Formalism.ZF.perron_integrable_Fy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:56:38.504816+00:00
-- url     : https://prove2.me/submissions/93dd735a-b577-487c-a77e-c0425cbbab12

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Theorems.Thm_Formalism_ZF_perron_norm_LSeries_le
import Theorems.Thm_Formalism_ZF_perron_denom_bound
import Theorems.Thm_Formalism_ZF_perron_Fy_eq_LSeries
import Theorems.Thm_Formalism_ZF_perron_continuous_Fy

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
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Integrable (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I)) := by
  have hm : 0 < min ((σ₀ - 1) ^ 2) 1 := lt_min (by nlinarith) one_pos
  have hS : 0 ≤ ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := tsum_nonneg fun n => norm_nonneg _
  have hbound : ∀ t : ℝ, ‖Fy y ((σ₀ : ℂ) + t * I)‖ ≤
      ((∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖) * y ^ σ₀ / min ((σ₀ - 1) ^ 2) 1) * (1 + t ^ 2)⁻¹ := by
    intro t
    have hre : 1 < ((σ₀ : ℂ) + t * I).re := by simpa using hσ
    have hre' : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp
    rw [perron_Fy_eq_LSeries y _ hre, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, hre']
    have hL := perron_norm_LSeries_le hσ ((σ₀ : ℂ) + t * I) hre'
    have hD := perron_denom_bound hσ t
    have hDpos : 0 < min ((σ₀ - 1) ^ 2) 1 * (1 + t ^ 2) := by positivity
    have hy' : 0 < y ^ σ₀ := Real.rpow_pos_of_pos hy σ₀
    calc ‖LSeries ↗Λ ((σ₀ : ℂ) + t * I)‖ * y ^ σ₀ / ‖((σ₀ : ℂ) + t * I) * ((σ₀ : ℂ) + t * I - 1)‖
        ≤ (∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖) * y ^ σ₀ / (min ((σ₀ - 1) ^ 2) 1 * (1 + t ^ 2)) :=
          div_le_div₀ (mul_nonneg hS hy'.le) (mul_le_mul_of_nonneg_right hL hy'.le) hDpos hD
      _ = _ := by field_simp
  exact Integrable.mono' ((integrable_inv_one_add_sq).const_mul _)
    (perron_continuous_Fy hy hσ).aestronglyMeasurable (Filter.Eventually.of_forall hbound)
end Formalism.ZF
