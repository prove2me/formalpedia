-- Prove2me | solution 1 for BookProof.ChapterMackeyQuasiInvariant.vmap_proj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:37:41.312924+00:00
-- url     : https://prove2.me/submissions/bde55129-7fdd-4b10-a7da-997bcf69f331

-- Generated from ChapterMackeyQuasiInvariant.lean — solution of BookProof.ChapterMackeyQuasiInvariant.vmap_proj
import Mathlib
import Definitions.Def_ChapterMackeyQuasiInvariant
import Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_proj_coeFn
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
theorem solution [SigmaFinite μ] (h : QuasiInvariant μ G) (hL : UnitaryCocycle μ L)
    (g : G) {E : Set X} (hE : MeasurableSet E) (f : Lp K 2 μ) :
    vmap h hL g (proj μ hE f)
      = proj μ ((actEquiv h.measurable g).measurableSet_image.mpr hE)
          (vmap h hL g f) := by

  refine Lp.ext ?_
  have e1 := vmap_coeFn h hL g (proj μ hE f)
  have e2 := proj_coeFn μ ((actEquiv h.measurable g).measurableSet_image.mpr hE)
    (vmap h hL g f)
  have e3 := vmap_coeFn h hL g f
  have e4 := (quasiMeasurePreserving h g⁻¹).ae_eq_comp (proj_coeFn μ hE f)
  filter_upwards [e1, e2, e3, e4] with x a1 a2 a3 a4
  simp only [Function.comp_apply] at a4
  by_cases hx : g⁻¹ • x ∈ E
  · have hmem : x ∈ (actEquiv h.measurable g) '' E := ⟨g⁻¹ • x, hx, by simp [actEquiv, smul_smul]⟩
    simp [vfun, hx, hmem, a1, a2, a3, a4]
  · have hmem : x ∉ (actEquiv h.measurable g) '' E := by
      rintro ⟨y, hy, rfl⟩
      exact hx (by simpa [actEquiv, smul_smul] using hy)
    simp [vfun, hx, hmem, a1, a2, a4]
