-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_sig_fib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:12:20.629463+00:00
-- url     : https://prove2.me/submissions/86b94738-cca6-4890-ab06-4b4f6b9f7ff2

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
theorem _root_.solution {A : Type*} {B : A → Type*} [Fintype A] [∀ a, Fintype (B a)] {Y : Type*} [DecidableEq Y]
    (ι : ∀ a, B a → Y) (P : A → Y → Prop) [∀ a y, Decidable (P a y)] (hι : ∀ a b, P a (ι a b)) (hu : ∀ a y, P a y → ∃! b, ι a b = y) (y : Y) :
    (Finset.univ.filter (fun p : (Σ a, B a) => ι p.1 p.2 = y)).card = (Finset.univ.filter (fun a => P a y)).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [← hp]
    exact hι a b
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' h
    simp only at h
    subst h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    have hP : P a y := by rw [← hp]; exact hι a b
    have hbb := (hu a y hP).unique hp hp'
    rw [hbb]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨b, hb, -⟩ := hu a y ha
    exact ⟨⟨a, b⟩, by simp [hb], rfl⟩
end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
