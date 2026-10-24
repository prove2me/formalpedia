-- Prove2me | solution 1 for FunctionalInequalities.Analysis.volume_subgradientImage_comp_affineEquiv_symm_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:11:16.795308+00:00
-- url     : https://prove2.me/submissions/68648bde-7413-437b-8bf4-38b0da08a6b3

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_subgradientImage_comp_affineEquiv_symm_408915f

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT11E1AffineTransportSubgradientimage
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section FiniteDimensional
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
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
  rw [FunctionalInequalities.Analysis.subgradientImage_comp_affineEquiv_symm_408915f]
  rw [MeasureTheory.Measure.addHaar_image_linearMap]
  rw [hdetabs]
