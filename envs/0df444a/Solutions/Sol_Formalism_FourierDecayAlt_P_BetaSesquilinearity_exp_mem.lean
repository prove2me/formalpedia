-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.exp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:38:06.523962+00:00
-- url     : https://prove2.me/submissions/54575dba-6e87-40d9-9014-c7268a89608b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Hsq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Hdet

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {X : Mat k r} (hX : inLie k r X) : NormedSpace.exp X ∈ GV k r := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hH : Hpk k r * Hpk k r = 1 := Hsq k r
  have hHu : IsUnit (Hpk k r) := (Matrix.isUnit_iff_isUnit_det _).mpr (Hdet k r)
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hH
  have hXH : Xᴴ = Hpk k r * (-X) * (Hpk k r)⁻¹ := by
    rw [hinv]
    have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX'
    calc Xᴴ = Xᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc, hH, Matrix.mul_one]
      _ = Hpk k r * (-X) * Hpk k r := by rw [h1, Matrix.mul_neg, Matrix.neg_mul]
  show (NormedSpace.exp X)ᴴ * Hpk k r * NormedSpace.exp X = Hpk k r
  rw [← Matrix.exp_conjTranspose, hXH, Matrix.exp_conj _ _ hHu, hinv, Matrix.exp_neg]
  have hu : IsUnit (NormedSpace.exp X).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp X)
  calc Hpk k r * (NormedSpace.exp X)⁻¹ * Hpk k r * Hpk k r * NormedSpace.exp X
      = Hpk k r * ((NormedSpace.exp X)⁻¹ * NormedSpace.exp X) := by
        rw [Matrix.mul_assoc (Hpk k r * _) (Hpk k r) (Hpk k r), hH, Matrix.mul_one, Matrix.mul_assoc]
    _ = Hpk k r := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
