-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.hasSum_re_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:43.716508+00:00
-- url     : https://prove2.me/submissions/6de484f1-d461-4525-a80a-d868a99adf26

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_Positivity
import Theorems.Thm_Formalism_ZeroFreeDirichlet_negLogDeriv_eq_LSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : HasSum (fun n ↦ (term (↗χ * ↗Λ) s n).re) (negLD χ s).re := by
  rw [negLogDeriv_eq_LSeries χ hs]
  exact Complex.hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs).hasSum
end Formalism.ZeroFreeDirichlet
