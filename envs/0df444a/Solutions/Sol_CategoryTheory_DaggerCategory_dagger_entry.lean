-- Prove2me | solution 1 for CategoryTheory.DaggerCategory.dagger_entry
-- status  : ACCEPTED   (prove)
-- author  : @Bingyu Xia
-- created : 2026-09-30T00:30:27.496394+00:00
-- url     : https://prove2.me/submissions/9b4d5736-9d15-4b8a-89d8-732391d66025

import Definitions.Def_CQM_DaggerCategory
import Definitions.Def_CQM_DaggerBiproduct
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Biproducts

open CategoryTheory Limits
open CategoryTheory.DaggerCategory
universe u u_1 u_2 v
lemma CategoryTheory.DaggerCategory.IsDaggerBiproduct.dagger_π {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type u_1} {f : ι → C} [CategoryTheory.Limits.HasBiproduct f] [CategoryTheory.DaggerCategory.IsDaggerBiproduct f] (i : ι) : (CategoryTheory.Limits.biproduct.π f i)† = CategoryTheory.Limits.biproduct.ι f i := by
  rw [← dagger_ι i]
  simp

theorem solution {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type u_1} {f : ι → C} [CategoryTheory.Limits.HasBiproduct f] [CategoryTheory.DaggerCategory.IsDaggerBiproduct f] {κ : Type u_2} {G : κ → C} [CategoryTheory.Limits.HasBiproduct G] [CategoryTheory.DaggerCategory.IsDaggerBiproduct G] (x : ⨁ f ⟶ ⨁ G) (i : ι) (j : κ) : CategoryTheory.DaggerCategory.entry x† j i = (CategoryTheory.DaggerCategory.entry x i j)† := by
  rw [entry, entry, ← IsDaggerBiproduct.dagger_π (f := G) j,
    ← IsDaggerBiproduct.dagger_ι (f := f) i]
  rw [← dagger_comp, ← dagger_comp, Category.assoc]
