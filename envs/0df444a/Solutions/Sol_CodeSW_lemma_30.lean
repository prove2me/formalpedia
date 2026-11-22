-- Prove2me | solution 1 for CodeSW.lemma_30
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T12:41:16.370837+00:00
-- url     : https://prove2.me/submissions/29076cb6-307c-4b21-b38f-ef48a94fff91

import Mathlib

open Matrix

theorem solution {K : Type*} [Field K] {k l j : ℕ} (A : Matrix (Fin k) (Fin l) K)
    (B : Matrix (Fin l) (Fin j) K) :
    Module.finrank K ↥(LinearMap.ker A.mulVecLin ⊓ LinearMap.range B.mulVecLin) +
        Module.finrank K (LinearMap.ker B.mulVecLin) =
      Module.finrank K (LinearMap.ker (A * B).mulVecLin) := by
  classical
  have hcomp : (A * B).mulVecLin = A.mulVecLin.comp B.mulVecLin := Matrix.mulVecLin_mul A B
  have hcomp_apply : ∀ x : Fin j → K, (A * B).mulVecLin x = A.mulVecLin (B.mulVecLin x) := by
    intro x
    rw [hcomp, LinearMap.comp_apply]
  -- the restriction of `B.mulVecLin` to the kernel of `(A * B).mulVecLin`
  set φ : ↥(LinearMap.ker (A * B).mulVecLin) →ₗ[K] (Fin l → K) :=
    B.mulVecLin.comp (Submodule.subtype (LinearMap.ker (A * B).mulVecLin)) with hφ
  have hφ_apply : ∀ x : ↥(LinearMap.ker (A * B).mulVecLin), φ x = B.mulVecLin x.1 := by
    intro x
    rw [hφ]
    rfl
  -- its range is `ker A ⊓ range B`
  have hrange : LinearMap.range φ = LinearMap.ker A.mulVecLin ⊓ LinearMap.range B.mulVecLin := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      rw [Submodule.mem_inf]
      constructor
      · rw [LinearMap.mem_ker, hφ_apply, ← hcomp_apply]
        exact (LinearMap.mem_ker).1 x.2
      · exact LinearMap.mem_range.2 ⟨x.1, (hφ_apply x).symm⟩
    · rintro y hy
      rw [Submodule.mem_inf] at hy
      obtain ⟨hyA, hyB⟩ := hy
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hyB
      refine LinearMap.mem_range.2 ⟨⟨x, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, hcomp_apply]
        exact (LinearMap.mem_ker).1 hyA
      · rw [hφ_apply]
  -- its kernel has the same dimension as `ker B.mulVecLin`
  have hker : Module.finrank K ↥(LinearMap.ker φ) =
      Module.finrank K (LinearMap.ker B.mulVecLin) := by
    let e : ↥(LinearMap.ker φ) ≃ₗ[K] ↥(LinearMap.ker B.mulVecLin) :=
      { toFun := fun x =>
          ⟨x.1.1, by
            have hx : φ x.1 = 0 := (LinearMap.mem_ker).1 x.2
            rw [hφ_apply] at hx
            exact (LinearMap.mem_ker).2 hx⟩
        invFun := fun y =>
          ⟨⟨y.1, by
            rw [LinearMap.mem_ker, hcomp_apply]
            have hy : B.mulVecLin y.1 = 0 := (LinearMap.mem_ker).1 y.2
            rw [hy, map_zero]⟩, by
            rw [LinearMap.mem_ker, hφ_apply]
            exact (LinearMap.mem_ker).1 y.2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl
        map_add' := fun x y => Subtype.ext rfl
        map_smul' := fun c x => Subtype.ext rfl }
    exact LinearEquiv.finrank_eq e
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange, hker] at hrn
  exact hrn
