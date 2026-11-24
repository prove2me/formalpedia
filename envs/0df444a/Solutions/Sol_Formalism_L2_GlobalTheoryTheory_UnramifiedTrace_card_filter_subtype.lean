-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_filter_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:12:19.496053+00:00
-- url     : https://prove2.me/submissions/e9924a7a-7109-4145-84b5-72c9c4a33f74

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
theorem _root_.solution {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    [Fintype {a // p a}] :
    (Finset.univ.filter (fun a : {a // p a} => q a.1)).card = (Finset.univ.filter (fun a => p a ∧ q a)).card := by
  refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨a.2, ha⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩
end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
