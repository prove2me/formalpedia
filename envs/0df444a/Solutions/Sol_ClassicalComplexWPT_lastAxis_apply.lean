-- Prove2me | solution 1 for ClassicalComplexWPT.lastAxis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:56:54.404403+00:00
-- url     : https://prove2.me/submissions/dfba276f-348c-4070-965c-99f214ddc99b

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_AnalyticSeries

set_option autoImplicit true
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (n : ℕ) (w : ℂ) : lastAxis n w = (0, w) := rfl
end ClassicalComplexWPT
