-- Prove2me | solution 1 for ClassicalComplexWPT.germ_isUnit_of_eventually_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:38.484658+00:00
-- url     : https://prove2.me/submissions/25c8903f-8fe0-4ea0-a621-68a34e259f42

import Definitions.Def_ClassicalComplexWPT_Basic
import Mathlib.Order.Filter.Germ.Basic
import Definitions.Def_ClassicalComplexWPT_Germs

set_option autoImplicit true
open Filter
open scoped Topology
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {X : Type*} {l : Filter X} {g : X → ℂ}
    (hg : ∀ᶠ x in l, g x ≠ 0) : IsUnit (g : Filter.Germ l ℂ) := by
  refine ⟨⟨(g : Filter.Germ l ℂ), (g⁻¹ : Filter.Germ l ℂ), ?_, ?_⟩, rfl⟩
  · apply Filter.Germ.coe_eq.mpr
    filter_upwards [hg] with x hx
    exact mul_inv_cancel₀ hx
  · apply Filter.Germ.coe_eq.mpr
    filter_upwards [hg] with x hx
    exact inv_mul_cancel₀ hx
end ClassicalComplexWPT
