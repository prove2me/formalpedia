-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PrismSpan.proj_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:12.680771+00:00
-- url     : https://prove2.me/submissions/f910e342-7846-47b4-b238-a8b90aca9325

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SpanQuadraticOfImage
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_diag_mem

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
theorem _root_.solution (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤) (i : Fin a)
    (X : Module.End k (W i)) : ∃ r ∈ alg ρ, r i = X := by
  have hX : X ∈ Submodule.span k (Set.range (ρ i)) := by rw [hspan i]; trivial
  induction hX using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact ⟨diag ρ g, diag_mem ρ g, rfl⟩
  | zero => exact ⟨0, Subalgebra.zero_mem _, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨r + s, add_mem hr hs, rfl⟩
  | smul c x _ hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨c • r, Subalgebra.smul_mem _ hr c, rfl⟩
end Formalism.CyclotomicNorms.PrismSpan
