-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_dual_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:12:16.227698+00:00
-- url     : https://prove2.me/submissions/acfbd0f5-01aa-4850-a6ee-efdc7b990411

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
theorem _root_.solution (te x : X) (hx : x ∈ Submodule.span K {te}) (hne : x ≠ te) :
    (Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1)).card = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro g - ⟨h1, h2⟩
  apply hne
  rw [map_smul, h1, smul_eq_mul, mul_one] at h2
  rw [h2, one_smul]
end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
