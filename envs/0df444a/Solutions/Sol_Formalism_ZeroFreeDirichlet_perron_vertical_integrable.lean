-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.perron_vertical_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:50:57.805237+00:00
-- url     : https://prove2.me/submissions/f04afbd7-9980-4448-8402-b279a9207e22

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
import Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_integrand_integrable
import Theorems.Thm_Formalism_ZeroFreeDirichlet_mellin_chebyshev_character

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
theorem _root_.solution {σ₀ : ℝ} (hσ : 1 < σ₀) :
    VerticalIntegrable (mellin (fun x : ℝ => Schi χ x)) (-σ₀) := by
  show Integrable (fun t : ℝ => mellin (fun x : ℝ => Schi χ x) (((-σ₀ : ℝ) : ℂ) + t * I))
  have h1 := (perron_integrand_integrable χ one_pos hσ).comp_neg
  refine h1.congr (Eventually.of_forall fun t => ?_)
  show Fchi χ 1 ((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I) =
    mellin (fun x : ℝ => Schi χ x) (((-σ₀ : ℝ) : ℂ) + t * I)
  have hw : ((-σ₀ : ℝ) : ℂ) + t * I = -((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I) := by push_cast; ring
  rw [hw, mellin_chebyshev_character χ (by simp [hσ])]
  unfold Fchi
  rw [ofReal_one, one_cpow, mul_one]
end Formalism.ZeroFreeDirichlet
