-- Prove2me | solution 1 for CategoryTheory.MonoidalCategory.Effect.complete_iff_kernel_iota_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Bingyu Xia
-- created : 2026-09-30T01:35:01.263894+00:00
-- url     : https://prove2.me/submissions/4a7adedd-566e-4114-9344-89e92a57c479

import Definitions.Def_CQM_DaggerCategory
import Definitions.Def_CQM_DaggerBiproduct
import Definitions.Def_CQM_MonoidalCategory
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Preadditive.Basic

open CategoryTheory Limits
open scoped BigOperators
open CategoryTheory.DaggerCategory
open CategoryTheory.MonoidalCategory
universe u v
theorem solution {C : Type u} [CategoryTheory.Category.{v, u} C] [CategoryTheory.MonoidalCategory C] [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type} {c : C} (x : ι → CategoryTheory.MonoidalCategory.Effect c) [CategoryTheory.Limits.HasBiproduct fun (x : ι) => CategoryTheory.MonoidalCategoryStruct.tensorUnit C] [CategoryTheory.Limits.HasKernel (CategoryTheory.Limits.biproduct.lift x)] : CategoryTheory.MonoidalCategory.Effect.Complete x ↔
  CategoryTheory.Limits.kernel.ι (CategoryTheory.Limits.biproduct.lift x) = 0 := by
  constructor
  · intro h
    exact h (kernel.ι (biproduct.lift x)) fun i => by
      rw [← biproduct.lift_π x i, ← Category.assoc, kernel.condition, zero_comp]
  · intro h c' f hf
    have hX : f ≫ biproduct.lift x = 0 := by
      apply biproduct.hom_ext
      intro i
      rw [Category.assoc, biproduct.lift_π, zero_comp]
      exact hf i
    calc f = kernel.lift (biproduct.lift x) f hX ≫ kernel.ι (biproduct.lift x) :=
          (kernel.lift_ι (biproduct.lift x) f hX).symm
      _ = kernel.lift (biproduct.lift x) f hX ≫ 0 := by rw [h]
      _ = 0 := comp_zero
