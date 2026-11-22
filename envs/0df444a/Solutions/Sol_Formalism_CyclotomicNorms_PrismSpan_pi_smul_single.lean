-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PrismSpan.pi_smul_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:51.442144+00:00
-- url     : https://prove2.me/submissions/84010fe5-c6c2-42ea-9a3b-d9b4a0a8b3b8

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SpanQuadraticOfImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.PrismSpan
variable {k G : Type} [Field k] [Group G] {a : ℕ} {W : Fin a → Type}
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
variable (ρ : ∀ i, Representation k G (W i))
namespace Formalism.CyclotomicNorms.PrismSpan
theorem _root_.solution (E : ∀ j, Module.End k (W j)) (i : Fin a) (w : W i) :
    E • (Pi.single i w : ∀ j, W j) = Pi.single i (E i w) := by
  funext j
  show E j (Pi.single i w j) = _
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]
end Formalism.CyclotomicNorms.PrismSpan
