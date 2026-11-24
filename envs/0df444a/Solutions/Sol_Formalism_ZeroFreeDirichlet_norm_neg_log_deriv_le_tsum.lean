-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.norm_neg_log_deriv_le_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:45:11.276775+00:00
-- url     : https://prove2.me/submissions/f38f0186-1336-4d2c-93f9-197da10d61b3

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
import Theorems.Thm_Formalism_ZeroFreeDirichlet_neg_log_deriv_eq_lseries_mul_vonMangoldt

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
theorem _root_.solution {σ₀ : ℝ} (hσ : 1 < σ₀) (w : ℂ) (hw : w.re = σ₀) :
    ‖negLD χ w‖ ≤ ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by
  have hw' : 1 < w.re := by rw [hw]; exact hσ
  rw [neg_log_deriv_eq_lseries_mul_vonMangoldt χ hw']
  have hs : LSeriesSummable (fun n => (Λ n : ℂ)) (σ₀ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hb : ∀ n, ‖LSeries.term (↗χ * ↗Λ) w n‖ ≤ ‖LSeries.term (fun n => (Λ n : ℂ)) (σ₀ : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs
    · exact le_rfl
    · rw [hw, Complex.ofReal_re]
      gcongr
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hsum : Summable fun n => ‖LSeries.term (↗χ * ↗Λ) w n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs.norm
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  first
  | exact tsum_le_tsum hb hsum hs.norm
  | exact Summable.tsum_le_tsum hb hsum hs.norm
end Formalism.ZeroFreeDirichlet
