-- Prove2me | solution 1 for ClassicalComplexWPT.exists_lastSlice_eq_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:34.181151+00:00
-- url     : https://prove2.me/submissions/e3c68c5a-d82a-49ea-94fe-674d35be9b41

import Definitions.Def_ClassicalComplexWPT_Basic
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Theorems.Thm_ClassicalComplexWPT_analyticAt_lastSlice
import Theorems.Thm_ClassicalComplexWPT_exactOrderInLastVariable_iff_analyticOrderAt
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastSlice_zero



set_option autoImplicit true
open scoped Topology
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ} {f : Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0) (horder : ExactOrderInLastVariable f d) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧
      lastSlice f =ᶠ[𝓝 0] fun w ↦ w ^ d * g w := by
  have hord : analyticOrderAt (lastSlice f) 0 = d :=
    (exactOrderInLastVariable_iff_analyticOrderAt hf).mp horder
  obtain ⟨g, hg, hg0, heq⟩ :=
    (AnalyticAt.analyticOrderAt_eq_natCast (analyticAt_lastSlice hf)).mp hord
  refine ⟨g, hg, hg0, ?_⟩
  filter_upwards [heq] with w hw
  simpa using hw
end ClassicalComplexWPT
