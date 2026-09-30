-- Prove2me | solution 1 for CategoryTheory.MonoidalCategory.Effect.isUnitary_lift_of_complete_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Bingyu Xia
-- created : 2026-09-30T01:43:03.357318+00:00
-- url     : https://prove2.me/submissions/19d14c7b-812f-4dd7-ab49-cd622801a211

import Definitions.Def_CQM_DaggerCategory
import Definitions.Def_CQM_DaggerBiproduct
import Definitions.Def_CQM_MonoidalCategory
import Theorems.Thm_CategoryTheory_MonoidalCategory_Effect_disjoint_iff_isIsometry_dagger
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

theorem solution {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.MonoidalCategory C] [CategoryTheory.Preadditive C] {ι : Type} {c : C} (x : ι → CategoryTheory.MonoidalCategory.Effect c) [CategoryTheory.Limits.HasBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] [CategoryTheory.DaggerCategory.IsDaggerBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] (hx : CategoryTheory.MonoidalCategory.Effect.Complete x) (hxd : CategoryTheory.MonoidalCategory.Effect.Disjoint x) : CategoryTheory.DaggerCategory.IsUnitary (CategoryTheory.Limits.biproduct.lift x) := by
  have hXX : (biproduct.lift x)† ≫ biproduct.lift x = 𝟙 (⨁ fun _ : ι ↦ 𝟙_ C) := by
    have h := (Effect.disjoint_iff_isIsometry_dagger x).mp hxd
    simpa only [involutive_dagger] using h.comp_dagger_eq_id
  have hy : biproduct.lift x ≫ (biproduct.lift x)† - 𝟙 c = 0 := by
    refine hx (biproduct.lift x ≫ (biproduct.lift x)† - 𝟙 c) ?_
    have hyX : (biproduct.lift x ≫ (biproduct.lift x)† - 𝟙 c) ≫ biproduct.lift x = 0 := by
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hXX, Category.comp_id,
        sub_self]
    intro i
    have := congrArg (fun m => m ≫ biproduct.π (fun _ : ι ↦ 𝟙_ C) i) hyX
    simpa [Category.assoc, biproduct.lift_π] using this
  let : IsIsometry (biproduct.lift x) := ⟨sub_eq_zero.mp hy⟩
  exact ⟨hXX⟩
