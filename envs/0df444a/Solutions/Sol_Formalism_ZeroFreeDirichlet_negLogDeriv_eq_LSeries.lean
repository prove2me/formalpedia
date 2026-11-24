-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.negLogDeriv_eq_LSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:44:11.001799+00:00
-- url     : https://prove2.me/submissions/d89da614-cbb6-49d3-80d5-4ecaa40c69d7

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_Positivity

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
    (hs : 1 < s.re) : negLD χ s = LSeries (↗χ * ↗Λ) s := by
  unfold negLD
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  ring
end Formalism.ZeroFreeDirichlet
