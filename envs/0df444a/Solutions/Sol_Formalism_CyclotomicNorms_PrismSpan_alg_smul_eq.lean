-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PrismSpan.alg_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:48.814313+00:00
-- url     : https://prove2.me/submissions/6f6217ac-2ea2-4dbb-9ae9-17e805dad0c4

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
theorem _root_.solution (c : k) (m : ∀ i, W i) : (algebraMap k (alg ρ) c) • m = c • m := by
  funext i
  show ((algebraMap k (alg ρ) c : ∀ i, Module.End k (W i))) i (m i) = c • m i
  simp
end Formalism.CyclotomicNorms.PrismSpan
