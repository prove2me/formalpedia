-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PrismSpan.semisimple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:47.631592+00:00
-- url     : https://prove2.me/submissions/b92a5fd4-7f5f-4c08-bb59-d3d2d94fffb8

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SpanQuadraticOfImage
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_sum_single
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_single_mem
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_coord_simple

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
theorem _root_.solution (hnt : ∀ i, Nontrivial (W i))
    (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤) :
    IsSemisimpleModule (alg ρ) (∀ j, W j) := by
  apply IsSemisimpleModule.of_sSup_simples_eq_top
  refine eq_top_iff.mpr fun v _ => ?_
  rw [← sum_single v]
  exact Submodule.sum_mem _ fun i _ =>
    (le_sSup (show coordSub ρ i ∈ {m : Submodule (alg ρ) (∀ j, W j) | IsSimpleModule _ m} from
      coord_simple hnt hspan i) : coordSub ρ i ≤ _) (single_mem i (v i))
end Formalism.CyclotomicNorms.PrismSpan
