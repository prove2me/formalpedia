-- Prove2me | solution 1 for BookProof.ChapterMackeyQuasiInvariant.mackey_inducedSystem_continuous
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:37:49.224173+00:00
-- url     : https://prove2.me/submissions/43ab16da-5d3a-45be-b2f9-5af3ab831ed9

-- Generated from ChapterMackeyQuasiInvariant.lean — solution of BookProof.ChapterMackeyQuasiInvariant.mackey_inducedSystem_continuous
import Mathlib
import Definitions.Def_ChapterMackeyQuasiInvariant
import Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_proj_idem
import Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_proj_univ
import Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_proj_symm
import Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_inducedSystem_covariance
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterMackeyQuasiInvariant



open MeasureTheory Measure


variable {G X K : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable {G X K : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable (μ : Measure X) (L : G → X → (K ≃ₗᵢ[ℂ] K))
variable {μ L}

set_option maxHeartbeats 1000000 in
theorem solution [SigmaFinite μ] (h : QuasiInvariant μ G)
    (hL : UnitaryCocycle μ L) :
    (∀ (g : G) (f₁ f₂ : Lp K 2 μ),
        vmap h hL g (f₁ + f₂) = vmap h hL g f₁ + vmap h hL g f₂) ∧
    (∀ (g : G) (c : ℂ) (f : Lp K 2 μ), vmap h hL g (c • f) = c • vmap h hL g f) ∧
    (∀ (g : G) (f : Lp K 2 μ), ‖vmap h hL g f‖ = ‖f‖) ∧
    (∀ f : Lp K 2 μ, vmap h hL (1 : G) f = f) ∧
    (∀ (g k : G) (f : Lp K 2 μ), vmap h hL g (vmap h hL k f) = vmap h hL (g * k) f) ∧
    (∀ (E : Set X) (hE : MeasurableSet E) (f : Lp K 2 μ),
        proj μ hE (proj μ hE f) = proj μ hE f) ∧
    (∀ f : Lp K 2 μ, proj μ MeasurableSet.univ f = f) ∧
    (∀ (E : Set X) (hE : MeasurableSet E) (f f' : Lp K 2 μ),
        (inner ℂ (proj μ hE f) f' : ℂ) = inner ℂ f (proj μ hE f')) ∧
    (∀ (g : G) (E : Set X) (hE : MeasurableSet E) (f : Lp K 2 μ),
        vmap h hL g (proj μ hE (vmap h hL g⁻¹ f))
          = proj μ ((actEquiv h.measurable g).measurableSet_image.mpr hE) f) :=
  ⟨vmap_add h hL, vmap_smul h hL, vmap_norm h hL, vmap_one h hL, vmap_mul h hL,
      fun _ hE f => proj_idem μ hE f, proj_univ μ, fun _ hE f f' => proj_symm μ hE f f',
      fun g _ hE f => inducedSystem_covariance h hL g hE f⟩
