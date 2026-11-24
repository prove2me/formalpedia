-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.sgs_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:08:48.373796+00:00
-- url     : https://prove2.me/submissions/80e41e1b-43a8-49cd-9bc4-cc489b88ad12

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_UWset_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_mem
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (hU : DilUW) (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) (g : Mat k r) :
    sgs (dilation₂ (x, y) p) (aDil k r x * g * (aDil k r y)⁻¹) = aDil k r x * sgs p g * (aDil k r y)⁻¹ := by
  obtain ⟨⟨h, n⟩, ⟨h', n'⟩⟩ := p
  have ua := WeylGroupFacts.isUnit_of_uh (aDil_mem k r hx)
  have ub := WeylGroupFacts.isUnit_of_uh (aDil_mem k r hy)
  have uh := WeylGroupFacts.isUnit_of_uh (UWset_sub k r _ hp.1)
  have uh' := WeylGroupFacts.isUnit_of_uh (UWset_sub k r _ hp.2.2.1)
  have k1 : aDil k r x * (Matrix.of h : Mat k r) = Matrix.of h * aDil k r x := hU k r D.z x _ hp.1
  have k2 : aDil k r y * (Matrix.of h' : Mat k r) = Matrix.of h' * aDil k r y := hU k r D.z' y _ hp.2.2.1
  have c1 : (Matrix.of h : Mat k r)⁻¹ * aDil k r x = aDil k r x * (Matrix.of h : Mat k r)⁻¹ := by
    calc (Matrix.of h : Mat k r)⁻¹ * aDil k r x
        = (Matrix.of h : Mat k r)⁻¹ * (aDil k r x * Matrix.of h) * (Matrix.of h : Mat k r)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uh, Matrix.mul_one]
      _ = aDil k r x * (Matrix.of h : Mat k r)⁻¹ := by
          rw [k1, Matrix.nonsing_inv_mul_cancel_left _ _ uh]
  have c2 : (aDil k r y)⁻¹ * (Matrix.of h' : Mat k r) = Matrix.of h' * (aDil k r y)⁻¹ := by
    calc (aDil k r y)⁻¹ * (Matrix.of h' : Mat k r)
        = (aDil k r y)⁻¹ * (Matrix.of h' * aDil k r y) * (aDil k r y)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ub, Matrix.mul_one]
      _ = Matrix.of h' * (aDil k r y)⁻¹ := by
          rw [← k2, Matrix.nonsing_inv_mul_cancel_left _ _ ub]
  have e1 : (aDil k r x * (Matrix.of n : Mat k r) * (aDil k r x)⁻¹)⁻¹ =
      aDil k r x * (Matrix.of n : Mat k r)⁻¹ * (aDil k r x)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ua, Matrix.mul_assoc]
  show (Matrix.of h : Mat k r)⁻¹ * (aDil k r x * (Matrix.of n : Mat k r) * (aDil k r x)⁻¹)⁻¹ *
      (aDil k r x * g * (aDil k r y)⁻¹) * (aDil k r y * (Matrix.of n' : Mat k r) * (aDil k r y)⁻¹) *
      (Matrix.of h' : Mat k r) =
    aDil k r x * ((Matrix.of h : Mat k r)⁻¹ * (Matrix.of n : Mat k r)⁻¹ * g * Matrix.of n' * Matrix.of h') *
      (aDil k r y)⁻¹
  rw [e1]
  calc (Matrix.of h : Mat k r)⁻¹ * (aDil k r x * (Matrix.of n : Mat k r)⁻¹ * (aDil k r x)⁻¹) *
      (aDil k r x * g * (aDil k r y)⁻¹) * (aDil k r y * (Matrix.of n' : Mat k r) * (aDil k r y)⁻¹) *
      (Matrix.of h' : Mat k r)
      = ((Matrix.of h : Mat k r)⁻¹ * aDil k r x) * (Matrix.of n : Mat k r)⁻¹ * ((aDil k r x)⁻¹ * aDil k r x) * g *
        ((aDil k r y)⁻¹ * aDil k r y) * Matrix.of n' * ((aDil k r y)⁻¹ * Matrix.of h') := by
        simp only [Matrix.mul_assoc]
    _ = (aDil k r x * (Matrix.of h : Mat k r)⁻¹) * (Matrix.of n : Mat k r)⁻¹ * 1 * g * 1 * Matrix.of n' *
        (Matrix.of h' * (aDil k r y)⁻¹) := by
        rw [c1, c2, Matrix.nonsing_inv_mul _ ua, Matrix.nonsing_inv_mul _ ub]
    _ = aDil k r x * ((Matrix.of h : Mat k r)⁻¹ * (Matrix.of n : Mat k r)⁻¹ * g * Matrix.of n' * Matrix.of h') *
        (aDil k r y)⁻¹ := by
        simp only [Matrix.mul_assoc, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.B6
