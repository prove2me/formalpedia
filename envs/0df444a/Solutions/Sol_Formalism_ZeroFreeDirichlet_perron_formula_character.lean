-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.perron_formula_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:08:18.204363+00:00
-- url     : https://prove2.me/submissions/9d92e43e-49ad-49c3-9113-416afd3c1a0a

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
import Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_integrand_integrable
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_continuousAt
import Theorems.Thm_Formalism_ZeroFreeDirichlet_mellin_chebyshev_character
import Theorems.Thm_Formalism_ZeroFreeDirichlet_mellin_convergent_chebyshev_character
import Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_vertical_integrable

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
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : PerronChi := by
  intro q _ χ y hy σ₀ hσ
  have hy0 : 0 < y := by linarith
  refine ⟨perron_integrand_integrable χ hy0 hσ, ?_⟩
  have hinv := mellinInv_mellin_eq (-σ₀) (fun x : ℝ => Schi χ x) hy0
    (mellin_convergent_chebyshev_character χ hσ) (perron_vertical_integrable χ hσ) (chebyshev_character_continuousAt χ y)
  rw [← hinv]
  unfold mellinInv
  have key : ∀ t : ℝ, (y : ℂ) ^ (-(((-σ₀ : ℝ) : ℂ) + t * I)) •
      mellin (fun x : ℝ => Schi χ x) (((-σ₀ : ℝ) : ℂ) + t * I) =
      Fchi χ y ((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    intro t
    have hw : ((-σ₀ : ℝ) : ℂ) + t * I = -((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I) := by push_cast; ring
    rw [hw, mellin_chebyshev_character χ (by simp [hσ]), neg_neg, smul_eq_mul]
    unfold Fchi
    ring
  rw [integral_congr_ae (Eventually.of_forall key)]
  have h2 : ∫ t : ℝ, Fchi χ y ((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I) =
      ∫ t : ℝ, Fchi χ y ((σ₀ : ℂ) + (t : ℂ) * I) :=
    integral_neg_eq_self (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + (t : ℂ) * I)) volume
  rw [h2, Complex.real_smul]
  push_cast
  ring
end Formalism.ZeroFreeDirichlet
