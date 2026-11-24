-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:38:14.819805+00:00
-- url     : https://prove2.me/submissions/efe183de-5fd7-4be3-9ca7-30fc7b65212b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_unit

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
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {X b : Mat k r} (hX : inLie k r X) (hb : b ∈ GV k r) : inLie k r (b⁻¹ * X * b) := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  have hu := gv_unit hb
  have h1 : b * b⁻¹ = 1 := Matrix.mul_nonsing_inv b hu
  have h2 : (b⁻¹)ᴴ * bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have e1 : Hpk k r * b⁻¹ = bᴴ * Hpk k r := by
    calc Hpk k r * b⁻¹ = bᴴ * Hpk k r * b * b⁻¹ := by rw [hb']
      _ = bᴴ * Hpk k r := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have e2 : (b⁻¹)ᴴ * Hpk k r = Hpk k r * b := by
    calc (b⁻¹)ᴴ * Hpk k r = (b⁻¹)ᴴ * (bᴴ * Hpk k r * b) := by rw [hb']
      _ = ((b⁻¹)ᴴ * bᴴ) * Hpk k r * b := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * b := by rw [h2, Matrix.one_mul]
  show (b⁻¹ * X * b)ᴴ * Hpk k r + Hpk k r * (b⁻¹ * X * b) = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc bᴴ * (Xᴴ * (b⁻¹)ᴴ) * Hpk k r + Hpk k r * (b⁻¹ * X * b)
      = bᴴ * Xᴴ * ((b⁻¹)ᴴ * Hpk k r) + (Hpk k r * b⁻¹) * X * b := by simp only [Matrix.mul_assoc]
    _ = bᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * b := by
        rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
