-- Prove2me | solution 2 for CategoryTheory.MonoidalCategory.Effect.disjoint_iff_isIsometry_dagger
-- status  : ACCEPTED   (prove)
-- author  : @Bingyu Xia
-- created : 2026-09-30T01:30:38.327802+00:00
-- url     : https://prove2.me/submissions/77abe5e6-5555-4ca9-afa6-91bf2baa8c33

import Definitions.Def_CQM_DaggerCategory
import Definitions.Def_CQM_DaggerBiproduct
import Definitions.Def_CQM_MonoidalCategory
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Preadditive.Basic

open CategoryTheory Limits
open scoped BigOperators
open CategoryTheory.DaggerCategory
open CategoryTheory.MonoidalCategory
universe u u_1 v
lemma CategoryTheory.DaggerCategory.IsDaggerBiproduct.dagger_π {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type u_1} {f : ι → C} [CategoryTheory.Limits.HasBiproduct f] [CategoryTheory.DaggerCategory.IsDaggerBiproduct f] (i : ι) : (CategoryTheory.Limits.biproduct.π f i)† = CategoryTheory.Limits.biproduct.ι f i := by
  rw [← dagger_ι i]
  simp

lemma CategoryTheory.MonoidalCategory.Effect.iota_lift_dagger {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.MonoidalCategory C] [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type} {c : C} (x : ι → CategoryTheory.MonoidalCategory.Effect c) [CategoryTheory.Limits.HasBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] [CategoryTheory.DaggerCategory.IsDaggerBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] (i : ι) : CategoryTheory.CategoryStruct.comp
    (CategoryTheory.Limits.biproduct.ι (fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C) i)
    (CategoryTheory.Limits.biproduct.lift x)† =
  (x i)† := by
  rw [← IsDaggerBiproduct.dagger_π (f := fun _ : ι ↦ 𝟙_ C) i, ← dagger_comp,
    biproduct.lift_π]

theorem solution {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.MonoidalCategory C] [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type} {c : C} (x : ι → CategoryTheory.MonoidalCategory.Effect c) [CategoryTheory.Limits.HasBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] [CategoryTheory.DaggerCategory.IsDaggerBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] : CategoryTheory.MonoidalCategory.Effect.Disjoint x ↔
  CategoryTheory.DaggerCategory.IsIsometry (CategoryTheory.Limits.biproduct.lift x)† := by
  constructor
  · intro h
    refine ⟨?_⟩
    simp only [involutive_dagger]
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc, Category.id_comp, biproduct.lift_π]
    apply biproduct.hom_ext'
    intro i
    rw [← Category.assoc, Effect.iota_lift_dagger x i]
    by_cases hij : i = j
    · subst hij
      rw [biproduct.ι_π_self, h.1 i]
    · rw [biproduct.ι_π_ne _ hij]
      exact h.2 (fun h => hij h.symm)
  · intro h
    have hh : (biproduct.lift x)† ≫ biproduct.lift x = 𝟙 (⨁ fun _ : ι ↦ 𝟙_ C) := by
      simpa only [involutive_dagger] using h.comp_dagger_eq_id
    have key : ∀ i j : ι, (x i)† ≫ x j
        = biproduct.ι (fun _ : ι ↦ 𝟙_ C) i ≫ biproduct.π (fun _ : ι ↦ 𝟙_ C) j := by
      intro i j
      calc (x i)† ≫ x j
          = biproduct.ι (fun _ : ι ↦ 𝟙_ C) i ≫ (biproduct.lift x)†
              ≫ biproduct.lift x ≫ biproduct.π (fun _ : ι ↦ 𝟙_ C) j := by
            rw [← Category.assoc, Effect.iota_lift_dagger x i, biproduct.lift_π]
        _ = biproduct.ι (fun _ : ι ↦ 𝟙_ C) i
              ≫ ((biproduct.lift x)† ≫ biproduct.lift x)
              ≫ biproduct.π (fun _ : ι ↦ 𝟙_ C) j := by
            simp only [Category.assoc]
        _ = biproduct.ι (fun _ : ι ↦ 𝟙_ C) i ≫ 𝟙 (⨁ fun _ : ι ↦ 𝟙_ C)
              ≫ biproduct.π (fun _ : ι ↦ 𝟙_ C) j := by
            rw [hh]
        _ = biproduct.ι (fun _ : ι ↦ 𝟙_ C) i
              ≫ biproduct.π (fun _ : ι ↦ 𝟙_ C) j := by
            rw [Category.id_comp]
    constructor
    · intro i
      rw [key i i, biproduct.ι_π_self]
    · intro i j hij
      rw [key j i, biproduct.ι_π_ne _ (fun h => hij h.symm)]
