-- Prove2me | solution 1 for DirichletUnitTheorem.tensor_real_algEquiv_prod
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:32:34.453449+00:00
-- url     : https://prove2.me/submissions/82522d9d-bb60-4935-ad87-cfacbc4f9232

import Mathlib
open NumberField

theorem solution (K : Type*) [Field K] [NumberField K] :
    Nonempty (TensorProduct ℚ ℝ K ≃ₐ[ℝ]
      ((Fin (InfinitePlace.nrRealPlaces K) → ℝ) × (Fin (InfinitePlace.nrComplexPlaces K) → ℂ))) := by
  classical
  let F : TensorProduct ℚ ℝ K →ₐ[ℝ] mixedEmbedding.mixedSpace K :=
    Algebra.TensorProduct.lift (Algebra.ofId ℝ _) (mixedEmbedding K).toRatAlgHom
      (fun _ _ => Commute.all _ _)
  have hsurj : Function.Surjective F.toLinearMap := by
    rw [← LinearMap.range_eq_top (f := F.toLinearMap), eq_top_iff,
      ← (mixedEmbedding.latticeBasis K).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨1 ⊗ₜ (integralBasis K i), ?_⟩
    simp [F]
    exact one_mul _
  have hrank : Module.finrank ℝ (TensorProduct ℚ ℝ K) =
      Module.finrank ℝ (mixedEmbedding.mixedSpace K) := by
    rw [Module.finrank_baseChange, mixedEmbedding.finrank]
  have hinj : Function.Injective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := F.toLinearMap) hrank).mpr hsurj
  let e₁ := AlgEquiv.ofBijective F ⟨hinj, hsurj⟩
  let e₂ : mixedEmbedding.mixedSpace K ≃ₐ[ℝ]
      ((Fin (InfinitePlace.nrRealPlaces K) → ℝ) × (Fin (InfinitePlace.nrComplexPlaces K) → ℂ)) :=
    AlgEquiv.prodCongr (AlgEquiv.piCongrLeft' ℝ (fun _ => ℝ) (Fintype.equivFin _))
      (AlgEquiv.piCongrLeft' ℝ (fun _ => ℂ) (Fintype.equivFin _))
  exact ⟨e₁.trans e₂⟩
