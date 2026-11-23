-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PrismSpan.single_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:12.842447+00:00
-- url     : https://prove2.me/submissions/39dc3f82-c191-4030-b126-93a21439d420

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
variable {ρ}
namespace Formalism.CyclotomicNorms.PrismSpan
theorem _root_.solution (i : Fin a) (w : W i) : (Pi.single i w : ∀ j, W j) ∈ coordSub ρ i :=
  fun _ hj => Pi.single_eq_of_ne hj w
end Formalism.CyclotomicNorms.PrismSpan
