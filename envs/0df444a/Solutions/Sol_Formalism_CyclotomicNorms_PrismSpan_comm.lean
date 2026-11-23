-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PrismSpan.comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:25.549784+00:00
-- url     : https://prove2.me/submissions/4bc73c12-a27d-47fb-8b53-5a8ce4968907

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SpanQuadraticOfImage
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_sum_single
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_pi_smul_single
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_off_diag
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_on_diag

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
    (hne : ∀ i j, i ≠ j → ¬ ∃ T : W i ≃ₗ[k] W j, ∀ g x, T (ρ i g x) = ρ j g (T x))
    (φ : (∀ j, W j) →ₗ[alg ρ] (∀ j, W j)) (E : ∀ j, Module.End k (W j)) (m : ∀ j, W j) :
    φ (E • m) = E • φ m := by
  have key : ∀ i (w : W i), φ (Pi.single i (E i w)) = E • φ (Pi.single i w) := by
    intro i w
    funext j
    show _ = E j (φ (Pi.single i w) j)
    by_cases hij : i = j
    · subst hij; exact on_diag hspan φ i (E i) w
    · rw [off_diag hspan hne φ hij, off_diag hspan hne φ hij, map_zero]
  conv_lhs => rw [← sum_single m]
  conv_rhs => rw [← sum_single m]
  simp only [Finset.smul_sum, map_sum, pi_smul_single, key]
end Formalism.CyclotomicNorms.PrismSpan
