-- Prove2me | solution 1 for FunctionalInequalities.Analysis.volume_subgradientImage_comp_affineEquiv_symm_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:32:48.107786+00:00
-- url     : https://prove2.me/submissions/2d227f26-73e2-4a0a-9a78-419287de35e5

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov
import Theorems.Thm_FunctionalInequalities_Analysis_subgradientImage_comp_affineEquiv_symm_readable

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT11E1AffineTransportSubgradientimage
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section FiniteDimensional
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- The volume of the transported subgradient image is `vol (∂u(G)) / |det T|`. -/
theorem solution [MeasurableSpace E] [BorelSpace E]
    (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage (u ∘ e.symm) (e '' G)) =
      ENNReal.ofReal |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ *
        (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u G) := by
  let b := stdOrthonormalBasis ℝ E
  have hdetadj :
      LinearMap.det (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E)) =
        LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) := by
    calc
      LinearMap.det (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E)) =
          (LinearMap.toMatrix b.toBasis b.toBasis
            (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E))).det :=
        (LinearMap.det_toMatrix b.toBasis
          (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E))).symm
      _ = (LinearMap.toMatrix b.toBasis b.toBasis
            (e.linear.symm : E →ₗ[ℝ] E)).conjTranspose.det := by
        rw [LinearMap.toMatrix_adjoint b b]
      _ = (LinearMap.toMatrix b.toBasis b.toBasis
            (e.linear.symm : E →ₗ[ℝ] E)).det := by
        rw [Matrix.det_conjTranspose]
        simp
      _ = LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) :=
        LinearMap.det_toMatrix b.toBasis (e.linear.symm : E →ₗ[ℝ] E)
  have hcomp :
      (e.linear.symm : E →ₗ[ℝ] E) ∘ₗ (e.linear : E →ₗ[ℝ] E) =
        LinearMap.id := by
    ext v
    simp
  have hprod :
      LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) *
          LinearMap.det (e.linear : E →ₗ[ℝ] E) = 1 := by
    calc
      LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) *
          LinearMap.det (e.linear : E →ₗ[ℝ] E) =
          LinearMap.det
            ((e.linear.symm : E →ₗ[ℝ] E) ∘ₗ (e.linear : E →ₗ[ℝ] E)) :=
        (LinearMap.det_comp (e.linear.symm : E →ₗ[ℝ] E)
          (e.linear : E →ₗ[ℝ] E)).symm
      _ = LinearMap.det LinearMap.id := by rw [hcomp]
      _ = 1 := LinearMap.det_id
  have hdet_ne :
      LinearMap.det (e.linear : E →ₗ[ℝ] E) ≠ 0 := by
    intro hzero
    have hbad : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) =
            LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) *
              LinearMap.det (e.linear : E →ₗ[ℝ] E) := hprod.symm
        _ = 0 := by rw [hzero]; simp
    exact zero_ne_one hbad.symm
  have hdet_symm :
      LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) =
        (LinearMap.det (e.linear : E →ₗ[ℝ] E))⁻¹ := by
    calc
      LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) =
          LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) * 1 := by simp
      _ = LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) *
          (LinearMap.det (e.linear : E →ₗ[ℝ] E) *
            (LinearMap.det (e.linear : E →ₗ[ℝ] E))⁻¹) := by
        rw [mul_inv_cancel₀ hdet_ne]
      _ = (LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) *
          LinearMap.det (e.linear : E →ₗ[ℝ] E)) *
            (LinearMap.det (e.linear : E →ₗ[ℝ] E))⁻¹ := by ring
      _ = (LinearMap.det (e.linear : E →ₗ[ℝ] E))⁻¹ := by
        rw [hprod]
        simp
  have hdetabs :
      |LinearMap.det (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E))| =
        |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ := by
    calc
      |LinearMap.det (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E))| =
          |LinearMap.det (e.linear.symm : E →ₗ[ℝ] E)| :=
        congrArg abs hdetadj
      _ = |(LinearMap.det (e.linear : E →ₗ[ℝ] E))⁻¹| :=
        congrArg abs hdet_symm
      _ = |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ :=
        abs_inv _
  rw [FunctionalInequalities.Analysis.subgradientImage_comp_affineEquiv_symm_readable]
  rw [MeasureTheory.Measure.addHaar_image_linearMap]
  rw [hdetabs]
