-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.prodProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:21:46.83243+00:00
-- url     : https://prove2.me/submissions/9a136ea1-de15-45af-a41f-e353eaf81456

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_proj_right
import Theorems.Thm_Formalism_MainNotions_PlaneGram_proj_preserves
import Theorems.Thm_Formalism_MainNotions_PlaneGram_bge_proj
import Theorems.Thm_Formalism_MainNotions_PlaneGram_bge_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
variable {L : Type} [Fintype L] [DecidableEq L] (sg : L → Bool) {r : ℕ} [NeZero r] (d : L → ℕ)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hP : PROJ K v p C0) (hD : DVRHyp v p) {ι : Type} (s : Finset ι)
    (S : ι → Finset L) (th : ι → ℤ)
    (hpair : ∀ x ∈ s, ∀ y ∈ s, S x ⊆ S y ∨ S y ⊆ S x ∨ Disjoint (S x) (S y)) :
    ∃ Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K,
      (∀ F ∈ PolK K r d, Pr F ∈ PolK K r d) ∧
      (∀ F ∈ PolK K r d, ∀ x ∈ s, Pr F ∈ Aset sg (S x) (th x)) ∧
      (∀ A ∈ PolK K r d, (∀ x ∈ s, A ∈ Aset sg (S x) (th x)) →
        ∀ G ∈ PolK K r d, fock A (Pr G) = fock A G) ∧
      (∀ F ∈ PolK K r d, ∀ a : ℝ, bge v a F →
        bge v (a - s.card * ((r : ℝ) ^ 2 * lg p r (2 * ∑ i, d i))) (Pr F)) ∧
      (∀ (S'' : Finset L) (th'' : ℤ), (∀ x ∈ s, S x ⊆ S'' ∨ Disjoint (S x) S'') →
        ∀ F ∈ PolK K r d, F ∈ Aset sg S'' th'' → Pr F ∈ Aset sg S'' th'') ∧
      (∀ i : L, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ (a : Fin r), ∀ F ∈ PolK K r d,
          Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨LinearMap.id, fun F hF => hF, fun F _ x hx => by simp at hx, fun A _ _ G _ => rfl, ?_,
      fun S'' th'' _ F _ hFW => hFW, fun i _ _ a F _ => rfl⟩
    intro F _ a ha
    simpa using ha
  | @insert x s hx ih =>
    have hpair' : ∀ y ∈ s, ∀ z ∈ s, S y ⊆ S z ∨ S z ⊆ S y ∨ Disjoint (S y) (S z) :=
      fun y hy z hz => hpair y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz)
    obtain ⟨Pr, h1, h2, h3, h4, h5, h6⟩ := ih hpair'
    obtain ⟨⟨πx, hπx⟩, -⟩ := hP hD L sg r d (S x) (th x)
    have hPx := (hP hD L sg r d (S x) (th x)).2 πx hπx
    refine ⟨πx ∘ₗ Pr, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro F hF
      exact (hπx _ (h1 F hF)).1
    · intro F hF y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hπx _ (h1 F hF)).2.1
      · exact proj_preserves sg d hP hD hπx
          (hpair _ (Finset.mem_insert_self _ s) y (Finset.mem_insert_of_mem hy)) (h1 F hF) (h2 F hF y hy)
    · intro A hA hAW G hG
      rw [LinearMap.comp_apply,
        fock_proj_right d hπx hA (hAW x (Finset.mem_insert_self x s)) (h1 G hG)]
      exact h3 A hA (fun y hy => hAW y (Finset.mem_insert_of_mem hy)) G hG
    · intro F hF a ha
      have hb := bge_proj sg d hP hD hπx (h1 F hF) (h4 F hF a ha)
      rw [LinearMap.comp_apply]
      refine bge_mono v ?_ hb
      rw [Finset.card_insert_eq_ite, if_neg hx]
      apply le_of_eq
      push_cast
      ring
    · intro S'' th'' hS F hF hFW
      have hPr := h5 S'' th'' (fun y hy => hS y (Finset.mem_insert_of_mem hy)) F hF hFW
      rw [LinearMap.comp_apply]
      rcases hS x (Finset.mem_insert_self x s) with h | h
      · exact proj_preserves sg d hP hD hπx (Or.inl h) (h1 F hF) hPr
      · exact proj_preserves sg d hP hD hπx (Or.inr (Or.inr h)) (h1 F hF) hPr
    · intro i hi hout a F hF
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        h6 i hi (fun y hy => hout y (Finset.mem_insert_of_mem hy)) a F hF]
      exact hPx.1 i hi (hout x (Finset.mem_insert_self x s)) a (Pr F) (h1 F hF)
end Formalism.MainNotions.PlaneGram
