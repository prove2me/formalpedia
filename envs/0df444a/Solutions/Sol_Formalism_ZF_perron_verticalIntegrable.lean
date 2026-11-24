-- Prove2me | solution 1 for Formalism.ZF.perron_verticalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:50:56.489835+00:00
-- url     : https://prove2.me/submissions/89e485e1-21d8-43ac-a894-1d5133fd3e4c

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Theorems.Thm_Formalism_ZF_perron_integrable_Fy
import Theorems.Thm_Formalism_ZF_perron_mellin_Sz

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
theorem _root_.solution {σ₀ : ℝ} (hσ : 1 < σ₀) :
    VerticalIntegrable (mellin (fun x : ℝ => (Formalism.Sz x : ℂ))) (-σ₀) := by
  unfold VerticalIntegrable
  have hF := (perron_integrable_Fy one_pos hσ).comp_neg
  have heq : (fun y : ℝ => mellin (fun x : ℝ => (Formalism.Sz x : ℂ)) (((-σ₀ : ℝ) : ℂ) + y * I)) =
      fun y : ℝ => Fy 1 ((σ₀ : ℂ) + ((-y : ℝ) : ℂ) * I) := by
    funext y
    have hre : 1 < ((σ₀ : ℂ) + ((-y : ℝ) : ℂ) * I).re := by simpa using hσ
    rw [show ((-σ₀ : ℝ) : ℂ) + y * I = -((σ₀ : ℂ) + ((-y : ℝ) : ℂ) * I) by push_cast; ring,
      perron_mellin_Sz hre]
    unfold Fy
    simp [Complex.one_cpow]
  rw [heq]
  exact hF
end Formalism.ZF
