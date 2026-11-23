-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PrismSpan.diag_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:56.317124+00:00
-- url     : https://prove2.me/submissions/527c1a2c-5df6-4614-bec9-574e2ce038de

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
theorem _root_.solution (g : G) : diag ρ g ∈ alg ρ :=
  ⟨MonoidAlgebra.single g 1, by simp⟩
end Formalism.CyclotomicNorms.PrismSpan
