-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.lseries_summable_of_vonMangoldt_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:44:06.880005+00:00
-- url     : https://prove2.me/submissions/268f91fc-85ce-4de5-949e-22241dce2875

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi

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
theorem _root_.solution {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1 * Λ n) {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (fun n => (a n : ℂ)) w := by
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hw
  have hb : ∀ n, ‖LSeries.term (fun n => (a n : ℂ)) w n‖ ≤ ‖LSeries.term (fun n => (Λ n : ℂ)) w n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs
    · exact le_rfl
    · gcongr
      have h2 := ha n
      have h3 : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      simpa [Complex.norm_real, abs_of_nonneg h3] using h2
  first
  | exact Summable.of_norm_bounded hΛ.norm hb
  | exact Summable.of_norm_bounded _ hΛ.norm hb
end Formalism.ZeroFreeDirichlet
