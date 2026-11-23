-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PrismSpan.exists_end
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:07.631829+00:00
-- url     : https://prove2.me/submissions/7defc475-5b68-400c-a601-c68d30ac53cd

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
theorem _root_.solution {V : Type} [AddCommGroup V] [Module k V] {v : V} (hv : v ≠ 0) (w : V) :
    ∃ X : Module.End k V, X v = w := by
  obtain ⟨μ, hμ⟩ := Module.Projective.exists_dual_ne_zero k hv
  exact ⟨(μ v)⁻¹ • μ.smulRight w, by simp [smul_smul, inv_mul_cancel₀ hμ]⟩
end Formalism.CyclotomicNorms.PrismSpan
