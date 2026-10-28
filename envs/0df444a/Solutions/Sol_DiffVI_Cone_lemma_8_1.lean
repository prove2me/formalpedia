-- Prove2me | solution 1 for DiffVI.Cone.lemma_8_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:25:38.232324+00:00
-- url     : https://prove2.me/submissions/21170497-c39f-49da-9cba-28ab71137c2a

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Cone_Setting

open scoped InnerProductSpace InnerProduct
open SolodovSvaiterVI.Alg21

open DiffVI.Cone in
theorem solution {m ℓ k p : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (E : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ℓ))
    (Z : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) (W : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hZW : IsZWBasis E Z W) :
    CondE K E ↔
      ∀ μ1 μ2 : EuclideanSpace ℝ (Fin k), ∀ lam1 lam2 : EuclideanSpace ℝ (Fin p),
        Z μ1 + W lam1 ∈ K → Z μ2 + W lam2 ∈ K → Z μ1 + W lam2 ∈ K := by
  obtain ⟨-, -, hZ, hW⟩ := hZW
  set S := LinearMap.ker (E : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin ℓ)) with hS
  have hZm : ∀ μ, Z μ ∈ S := fun μ => by
    rw [← hZ]; exact LinearMap.mem_range_self _ μ
  have hWm : ∀ lam, W lam ∈ Sᗮ := fun lam => by
    rw [← hW]; exact LinearMap.mem_range_self _ lam
  have p1 : ∀ μ lam, S.starProjection (Z μ + W lam) = Z μ := by
    intro μ lam
    rw [map_add, Submodule.starProjection_eq_self_iff.mpr (hZm μ),
      (Submodule.starProjection_apply_eq_zero_iff S).mpr (hWm lam), add_zero]
  have p2 : ∀ μ lam, Sᗮ.starProjection (Z μ + W lam) = W lam := by
    intro μ lam
    rw [map_add, Submodule.starProjection_eq_self_iff.mpr (hWm lam),
      Submodule.starProjection_orthogonal_apply_eq_zero (hZm μ), zero_add]
  constructor
  · intro h μ1 μ2 lam1 lam2 h1 h2
    have := h _ h1 _ h2
    rwa [p1, p2] at this
  · intro h u1 hu1 u2 hu2
    have hd : ∀ u, ∃ μ lam, u = Z μ + W lam := by
      intro u
      have a : S.starProjection u ∈ LinearMap.range (Z : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
        rw [hZ]; exact Submodule.starProjection_apply_mem _ _
      have b : Sᗮ.starProjection u ∈ LinearMap.range (W : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
        rw [hW]; exact Submodule.starProjection_apply_mem _ _
      obtain ⟨μ, hμ⟩ := a
      obtain ⟨lam, hlam⟩ := b
      refine ⟨μ, lam, ?_⟩
      have := Submodule.starProjection_add_starProjection_orthogonal (K := S) u
      rw [← this]
      simp only [ContinuousLinearMap.coe_coe] at hμ hlam
      rw [hμ, hlam]
    obtain ⟨μ1, lam1, rfl⟩ := hd u1
    obtain ⟨μ2, lam2, rfl⟩ := hd u2
    rw [p1, p2]
    exact h μ1 μ2 lam1 lam2 hu1 hu2
