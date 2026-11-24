-- Prove2me | solution 1 for FiniteEnergyPlane.exists_local_page_family
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-22T18:10:40.994919+00:00
-- url     : https://prove2.me/submissions/5bece1bb-0bf0-457e-848d-16be928d5f31

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_proj_not_mem_range_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_exists_pageFamily_injective_fderiv
import Theorems.Thm_FiniteEnergyPlane_injOn_pageMap_of_isPageFamilyOn
import Theorems.Thm_FiniteEnergyPlane_exists_eq_shiftA_comp_affine_of_isPageFamilyOn



/-!
# Hryniewicz Lemmas 7.2/7.3 (`exists_local_page_family`): glue over three children

* (C) a `C^l` page family through `u₀` whose `pageMap` has injective derivative;
* (I) `pageMap` of any `C^l` page family is injective near each `t₀`;
* (N) nearby embedded fast planes are, up to shift and affine change, slices of any page family
  through `u₀`;
* `x(ℝ)` is avoided slice by slice (Lemma 6.24).
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_local_page_family_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (t₀ : ℝ) (u₀ : ℂ → V 1) (hu₀ : u₀ ∈ embeddedFastPlaneSet H J P {y t₀} γ)
    (l : ℕ) (hl : 1 ≤ l) :
    ∃ ε > 0, ∃ U : ℝ × ℂ → V 1, IsPageFamilyOn H J P γ y l (ball t₀ ε) U ∧
      (∀ z, U (t₀, z) = u₀ z) ∧
      Set.InjOn (pageMap H U) (ball t₀ ε ×ˢ Set.univ) ∧
      (∀ p ∈ ball t₀ ε ×ˢ (Set.univ : Set ℂ),
        Function.Injective (fderiv ℝ (pageMap H U) p) ∧ pageMap H U p ∉ Set.range P.x) ∧
      ∀ v : ℕ → ℂ → V 1,
        (∀ k, IsFastPlane H J (v k) ∧ IsNondegenerateEnd H (v k) cylInf P 1 ∧
          IsEmbeddedPlane (v k)) →
        JHolomorphic.TendstoCInftyLocOn v u₀ Set.univ →
        ∃ (A B : ℕ → ℂ) (r t : ℕ → ℝ), Tendsto A atTop (𝓝 1) ∧ Tendsto B atTop (𝓝 0) ∧
          Tendsto r atTop (𝓝 0) ∧ Tendsto t atTop (𝓝 t₀) ∧
          ∀ᶠ k in atTop, t k ∈ ball t₀ ε ∧
            ∀ z, U (t k, z) = shiftA (r k) (v k) (A k * z + B k) := by
  obtain ⟨ε₁, hε₁, U, hU, hU0, hUd⟩ :=
    exists_pageFamily_injective_fderiv H hH J hJ P hcz γ y hy t₀ u₀ hu₀ l hl
  obtain ⟨ε, hε, hsub, hinj⟩ := injOn_pageMap_of_isPageFamilyOn H hH J hJ P hcz γ y hy l hl
    (ball t₀ ε₁) isOpen_ball U hU t₀ (mem_ball_self hε₁)
  have hU' : IsPageFamilyOn H J P γ y l (ball t₀ ε) U :=
    ⟨hU.1.mono (Set.prod_mono hsub le_rfl), fun t ht => hU.2 t (hsub ht)⟩
  have hfun : (fun z => U (t₀, z)) = u₀ := funext hU0
  refine ⟨ε, hε, U, hU', hU0, hinj, fun p hp => ⟨hUd p (Set.prod_mono hsub le_rfl hp), ?_⟩, ?_⟩
  · obtain ⟨t, z⟩ := p
    have hm := hU'.2 t hp.1
    exact proj_not_mem_range_of_isFastPlane H hH J hJ P hcz (fun z => U (t, z)) hm.1.1
      hm.1.2.1 hm.2 z
  · intro v hv hvlim
    rw [← hfun] at hvlim
    exact exists_eq_shiftA_comp_affine_of_isPageFamilyOn H hH J hJ P hcz γ y hy l hl
      (ball t₀ ε) isOpen_ball U hU' t₀ (mem_ball_self hε) v hv hvlim

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (t₀ : ℝ) (u₀ : ℂ → V 1) (hu₀ : u₀ ∈ embeddedFastPlaneSet H J P {y t₀} γ)
    (l : ℕ) (hl : 1 ≤ l) :
    ∃ ε > 0, ∃ U : ℝ × ℂ → V 1, IsPageFamilyOn H J P γ y l (ball t₀ ε) U ∧
      (∀ z, U (t₀, z) = u₀ z) ∧
      Set.InjOn (pageMap H U) (ball t₀ ε ×ˢ Set.univ) ∧
      (∀ p ∈ ball t₀ ε ×ˢ (Set.univ : Set ℂ),
        Function.Injective (fderiv ℝ (pageMap H U) p) ∧ pageMap H U p ∉ Set.range P.x) ∧
      ∀ v : ℕ → ℂ → V 1,
        (∀ k, IsFastPlane H J (v k) ∧ IsNondegenerateEnd H (v k) cylInf P 1 ∧
          IsEmbeddedPlane (v k)) →
        JHolomorphic.TendstoCInftyLocOn v u₀ Set.univ →
        ∃ (A B : ℕ → ℂ) (r t : ℕ → ℝ), Tendsto A atTop (𝓝 1) ∧ Tendsto B atTop (𝓝 0) ∧
          Tendsto r atTop (𝓝 0) ∧ Tendsto t atTop (𝓝 t₀) ∧
          ∀ᶠ k in atTop, t k ∈ ball t₀ ε ∧
            ∀ z, U (t k, z) = shiftA (r k) (v k) (A k * z + B k) :=
  exists_local_page_family_aux H hH J hJ P hcz γ y hy t₀ u₀ hu₀ l hl
