-- Prove2me | solution 1 for ClassicalComplexWPT.analytic_germ_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:14:49.702615+00:00
-- url     : https://prove2.me/submissions/e41be802-a76a-496d-9859-7af1bf4bfe97

import Definitions.Def_ClassicalComplexWPT_Basic
import Mathlib.Order.Filter.Germ.Basic
import Definitions.Def_ClassicalComplexWPT_Germs
import Theorems.Thm_ClassicalComplexWPT_germ_isUnit_of_eventually_ne

set_option autoImplicit true
open Filter
open scoped Topology
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : E → ℂ} {x : E} (hg : AnalyticAt ℂ g x) (hg0 : g x ≠ 0) :
    IsUnit (g : Filter.Germ (𝓝 x) ℂ) := by
  apply germ_isUnit_of_eventually_ne
  exact hg.continuousAt.eventually_ne hg0
end ClassicalComplexWPT
