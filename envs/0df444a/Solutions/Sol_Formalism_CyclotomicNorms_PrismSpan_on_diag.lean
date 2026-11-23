-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PrismSpan.on_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:49.997854+00:00
-- url     : https://prove2.me/submissions/f3903a73-503d-4437-85c8-e7313d14fdf2

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SpanQuadraticOfImage
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_pi_smul_single
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_proj_surj

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
theorem _root_.solution (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤)
    (φ : (∀ j, W j) →ₗ[alg ρ] (∀ j, W j)) (i : Fin a) (X : Module.End k (W i)) (w : W i) :
    φ (Pi.single i (X w)) i = X (φ (Pi.single i w) i) := by
  obtain ⟨r, hr, rfl⟩ := proj_surj hspan i X
  rw [← pi_smul_single r i w]
  exact congrFun (φ.map_smul ⟨r, hr⟩ (Pi.single i w)) i
end Formalism.CyclotomicNorms.PrismSpan
