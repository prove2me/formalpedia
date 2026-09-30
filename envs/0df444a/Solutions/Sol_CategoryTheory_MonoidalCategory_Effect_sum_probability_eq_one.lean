-- Prove2me | solution 1 for CategoryTheory.MonoidalCategory.Effect.sum_probability_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Bingyu Xia
-- created : 2026-09-30T01:53:20.161399+00:00
-- url     : https://prove2.me/submissions/fe54126f-b585-456b-abc8-4952775db9c5

import Definitions.Def_CQM_DaggerCategory
import Definitions.Def_CQM_DaggerBiproduct
import Definitions.Def_CQM_MonoidalCategory
import Theorems.Thm_CategoryTheory_MonoidalCategory_Effect_disjoint_iff_isIsometry_dagger
import Theorems.Thm_CategoryTheory_MonoidalCategory_Effect_isUnitary_lift_of_complete_disjoint
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

lemma CategoryTheory.MonoidalCategory.Effect.lift_comp_dagger_eq_sum {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.MonoidalCategory C] [CategoryTheory.Preadditive C] {ι : Type} [Fintype ι] {c : C} (x : ι → CategoryTheory.MonoidalCategory.Effect c) [CategoryTheory.Limits.HasBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] [CategoryTheory.DaggerCategory.IsDaggerBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.biproduct.lift x) (CategoryTheory.Limits.biproduct.lift x)† =
  ∑ i : ι, CategoryTheory.CategoryStruct.comp (x i) (x i)† := by
  calc biproduct.lift x ≫ (biproduct.lift x)†
      = biproduct.lift x ≫ (∑ i, biproduct.π (fun _ : ι ↦ 𝟙_ C) i
            ≫ biproduct.ι (fun _ : ι ↦ 𝟙_ C) i) ≫ (biproduct.lift x)† := by
        rw [biproduct.total, Category.id_comp]
    _ = ∑ i, x i ≫ (x i)† := by
        rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Category.assoc, biproduct.lift_π, Category.assoc, Effect.iota_lift_dagger]

theorem solution {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.MonoidalCategory C] [CategoryTheory.Preadditive C] {ι : Type} [Fintype ι] {c : C} (x : ι → CategoryTheory.MonoidalCategory.Effect c) [CategoryTheory.Limits.HasBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] [CategoryTheory.DaggerCategory.IsDaggerBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] (hx : CategoryTheory.MonoidalCategory.Effect.Complete x) (hxd : CategoryTheory.MonoidalCategory.Effect.Disjoint x) (a : CategoryTheory.MonoidalCategory.State c) (ha : CategoryTheory.DaggerCategory.IsIsometry a) : ∑ i : ι, CategoryTheory.MonoidalCategory.probability a (x i) =
  CategoryTheory.CategoryStruct.id (CategoryTheory.MonoidalCategoryStruct.tensorUnit C) := by
  have hunit : IsUnitary (biproduct.lift x) :=
    Effect.isUnitary_lift_of_complete_disjoint x hx hxd
  have hXX : biproduct.lift x ≫ (biproduct.lift x)† = 𝟙 c :=
    IsIsometry.comp_dagger_eq_id (biproduct.lift x)
  calc ∑ i, probability a (x i)
      = ∑ i, (a ≫ (x i ≫ (x i)†)) ≫ a† := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [probability, Category.assoc]
    _ = a ≫ (∑ i, x i ≫ (x i)†) ≫ a† := by
        rw [← Preadditive.sum_comp, ← Preadditive.comp_sum, Category.assoc]
    _ = a ≫ (biproduct.lift x ≫ (biproduct.lift x)†) ≫ a† := by
        rw [Effect.lift_comp_dagger_eq_sum]
    _ = a ≫ 𝟙 c ≫ a† := by rw [hXX]
    _ = a ≫ a† := by rw [Category.id_comp]
    _ = 𝟙 (𝟙_ C) := ha.comp_dagger_eq_id
