-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.exists_dual_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:34.558807+00:00
-- url     : https://prove2.me/submissions/6bda2529-8f21-4588-850a-ee0b1c749e45

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_UnramifiedTrace_CardFilterSubtype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
variable {K X : Type*} [Field K] [Fintype K] [DecidableEq K] [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [Fintype (Module.Dual K X)]
namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
theorem _root_.solution {Y : Type*} [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] (y : Y) (hy : y ≠ 0) :
    ∃ g : Module.Dual K Y, g y = 1 := by
  have h1 : ∃ g : Module.Dual K Y, g y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy ((Module.forall_dual_apply_eq_zero_iff K y).1 h)
  obtain ⟨g, hg⟩ := h1
  exact ⟨(g y)⁻¹ • g, by simp [hg]⟩
end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
