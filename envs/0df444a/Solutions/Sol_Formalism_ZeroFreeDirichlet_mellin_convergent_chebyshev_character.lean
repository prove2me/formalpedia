-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.mellin_convergent_chebyshev_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:49:44.363027+00:00
-- url     : https://prove2.me/submissions/d7a228e2-d325-4ae1-830f-2e9a7208e513

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_eq_zero_of_le_one
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_integrableOn

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
    MellinConvergent (fun x : ℝ => Schi χ x) ((-σ₀ : ℝ) : ℂ) := by
  unfold MellinConvergent
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_zero).congr_fun (fun x hx => ?_) measurableSet_Ioc
    simp [chebyshev_character_eq_zero_of_le_one χ hx.2]
  · have h := chebyshev_character_integrableOn χ (w := (σ₀ : ℂ)) (by simpa using hσ)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [ofReal_neg]
end Formalism.ZeroFreeDirichlet
