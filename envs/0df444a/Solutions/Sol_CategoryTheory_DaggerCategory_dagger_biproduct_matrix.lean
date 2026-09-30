-- Prove2me | solution 1 for CategoryTheory.DaggerCategory.dagger_biproduct_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Bingyu Xia
-- created : 2026-09-30T01:22:33.825287+00:00
-- url     : https://prove2.me/submissions/68477fc8-b133-4ace-b147-60e2218868a3

import Definitions.Def_CQM_DaggerCategory
import Definitions.Def_CQM_DaggerBiproduct
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Biproducts

open CategoryTheory Limits
open CategoryTheory.DaggerCategory
universe u u_1 v
lemma CategoryTheory.DaggerCategory.IsDaggerBiproduct.dagger_π {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type u_1} {f : ι → C} [CategoryTheory.Limits.HasBiproduct f] [CategoryTheory.DaggerCategory.IsDaggerBiproduct f] (i : ι) : (CategoryTheory.Limits.biproduct.π f i)† = CategoryTheory.Limits.biproduct.ι f i := by
  rw [← dagger_ι i]
  simp

theorem solution {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.DaggerCategory C] [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type} {κ : Type} [Finite ι] [Finite κ] {F : ι → C} {G : κ → C} [CategoryTheory.Limits.HasFiniteBiproducts C] [CategoryTheory.DaggerCategory.IsDaggerBiproduct F] [CategoryTheory.DaggerCategory.IsDaggerBiproduct G] (m : (i : ι) → (j : κ) → F i ⟶ G j) : (CategoryTheory.Limits.biproduct.matrix m)† = CategoryTheory.Limits.biproduct.matrix fun (j : κ) (i : ι) => (m i j)† := by
  apply biproduct.matrixEquiv.injective
  funext j i
  change biproduct.components ((biproduct.matrix m)†) j i
      = biproduct.components (biproduct.matrix fun (j : κ) (i : ι) => (m i j)†) j i
  rw [biproduct.matrix_components, biproduct.components]
  rw [← IsDaggerBiproduct.dagger_π (f := G) j, ← IsDaggerBiproduct.dagger_ι (f := F) i]
  rw [← dagger_comp, ← dagger_comp]
  rw [Category.assoc, ← biproduct.components, biproduct.matrix_components]
