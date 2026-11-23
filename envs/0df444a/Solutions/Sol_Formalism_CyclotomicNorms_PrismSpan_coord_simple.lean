-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PrismSpan.coord_simple
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:49.729913+00:00
-- url     : https://prove2.me/submissions/52f1fd55-7e0f-4f53-be65-21d1fa0961af

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SpanQuadraticOfImage
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_proj_surj
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_exists_end
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_single_mem

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
    (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤) (i : Fin a) :
    IsSimpleModule (alg ρ) (coordSub ρ i) := by
  rw [isSimpleModule_iff_isAtom]
  refine ⟨?_, fun N hN => ?_⟩
  · obtain ⟨w, hw⟩ := exists_ne (0 : W i)
    intro h
    have h1 : (Pi.single i w : ∀ j, W j) ∈ (⊥ : Submodule (alg ρ) (∀ j, W j)) :=
      h ▸ single_mem i w
    rw [Submodule.mem_bot] at h1
    exact hw (by simpa using congrFun h1 i)
  · by_contra hN0
    obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
    have hvi : v i ≠ 0 := by
      intro h
      apply hv0
      funext j
      by_cases hj : j = i
      · subst hj; exact h
      · exact hN.le hvN j hj
    refine hN.ne (le_antisymm hN.le fun u hu => ?_)
    obtain ⟨X, hX⟩ := exists_end (k := k) hvi (u i)
    obtain ⟨r, hr, rfl⟩ := proj_surj hspan i X
    have h2 : (⟨r, hr⟩ : alg ρ) • v = u := by
      funext j
      show r j (v j) = u j
      by_cases hj : j = i
      · subst hj; exact hX
      · rw [hN.le hvN j hj, hu j hj, map_zero]
    exact h2 ▸ N.smul_mem _ hvN
end Formalism.CyclotomicNorms.PrismSpan
