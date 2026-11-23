-- Prove2me | solution 1 for Formalism.CountingSumsFrames.wach_cohomology_top_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:12.34081+00:00
-- url     : https://prove2.me/submissions/a6104c83-0be3-4727-82af-42b9f9ccca57

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_LemmaS
import Theorems.Thm_Formalism_CountingSumsFrames_GoodRankMultinomialDepth_gr_comp
import Theorems.Thm_Formalism_CountingSumsFrames_GoodRankMultinomialDepth_gr_goodRank
import Theorems.Thm_Formalism_CountingSumsFrames_GoodRankMultinomialDepth_goodRank_mono
import Theorems.Thm_Formalism_CountingSumsFrames_GoodRankMultinomialDepth_gr_of_primitive
import Theorems.Thm_Formalism_CountingSumsFrames_GoodRankMultinomialDepth_split

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
open Formalism Formalism.CountingSumsFrames
open GoodRankMultinomialDepth
namespace Formalism.CountingSumsFrames
theorem _root_.solution : LemmaS := by
  intro O _ _ _ π hπ C Cp R R'' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ io ph ps D ρp σ np h1 h2 h3
  classical
  obtain ⟨u1, v1, huv1⟩ := h1
  obtain ⟨u2, v2, huv2⟩ := h2
  have e1 : ∀ y, v1 (ps (ph (u1 y))) = π ^ D • y := fun y => LinearMap.congr_fun huv1 y
  have e2 : ∀ x, v2 (ph (io (u2 x))) = π ^ D • x := fun x => LinearMap.congr_fun huv2 x
  obtain ⟨p, j0, j1, hi, hii, hiii⟩ := split hπ (2 * D) σ (ps ∘ₗ ph ∘ₗ io ∘ₗ u2)
  have hgood : GR {k // ¬ p k} π (ps ∘ₗ ph ∘ₗ io) (2 * D) :=
    gr_comp (u2 ∘ₗ j1) (gr_of_primitive hπ (2 * D) _ (fun x z hxz => hiii x z hxz))
  let hmap : ({k // p k} ⊕ Fin ρp → O) →ₗ[O] Cp :=
    io ∘ₗ u2 ∘ₗ j0 ∘ₗ LinearMap.funLeft O O Sum.inl + u1 ∘ₗ LinearMap.funLeft O O Sum.inr
  have hbad : GR ({k // p k} ⊕ Fin ρp) π ph (2 * D) := by
    refine gr_comp hmap (gr_of_primitive hπ (2 * D) _ ?_)
    intro w z hwz
    have hw : ph (io (u2 (j0 (fun k => w (Sum.inl k))))) + ph (u1 (fun k => w (Sum.inr k))) =
        π ^ (2 * D + 1) • z := by
      rw [← map_add]
      exact hwz
    suffices H : ∀ (x : {k // p k} → O) (y : Fin ρp → O),
        ph (io (u2 (j0 x))) + ph (u1 y) = π ^ (2 * D + 1) • z →
        (∀ k, π ∣ x k) ∧ ∀ k, π ∣ y k by
      obtain ⟨hx, hy⟩ := H _ _ hw
      rintro (k | k)
      · exact hx k
      · exact hy k
    intro x y hw
    obtain ⟨z0, hz0⟩ := hi x
    have hz0' : ps (ph (io (u2 (j0 x)))) = π ^ (2 * D + 1) • z0 := hz0
    have hy1 : ps (ph (u1 y)) = π ^ (2 * D + 1) • (ps z - z0) := by
      have := congrArg ps hw
      rw [map_add, map_smul] at this
      rw [smul_sub, ← this, ← hz0']
      abel
    have hy2 : π ^ D • y = π ^ D • (π ^ (D + 1) • v1 (ps z - z0)) := by
      rw [← e1, hy1, map_smul, smul_smul, ← pow_add, show D + (D + 1) = 2 * D + 1 by ring]
    have hy : y = π ^ (D + 1) • v1 (ps z - z0) :=
      smul_right_injective _ (pow_ne_zero D hπ.ne_zero) hy2
    have hw' : ph (io (u2 (j0 x))) + ph (u1 y) = π ^ (2 * D + 1) • z := hw
    have hx1 : ph (io (u2 (j0 x))) = π ^ (D + 1) • (π ^ D • z - ph (u1 (v1 (ps z - z0)))) := by
      rw [smul_sub, smul_smul, ← pow_add, show D + 1 + D = 2 * D + 1 by ring, ← hw', hy,
        map_smul, map_smul]
      abel
    have hjx : j0 x = π • v2 (π ^ D • z - ph (u1 (v1 (ps z - z0)))) := by
      have := e2 (j0 x)
      rw [hx1, map_smul, pow_succ, mul_smul] at this
      exact (smul_right_injective _ (pow_ne_zero D hπ.ne_zero) this).symm
    refine ⟨hii x _ hjx, fun k => ?_⟩
    rw [hy, Pi.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_right (dvd_pow_self π (Nat.succ_ne_zero D)) _
  have hcard := h3 _ (gr_goodRank hbad)
  rw [Fintype.card_sum, Fintype.card_fin] at hcard
  have hle := Fintype.card_subtype_le p
  have hsum := Fintype.card_subtype_compl p
  rw [Fintype.card_fin] at hle hsum
  apply goodRank_mono (gr_goodRank hgood)
  omega
end Formalism.CountingSumsFrames
