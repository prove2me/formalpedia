-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:36:28.484971+00:00
-- url     : https://prove2.me/submissions/878837e0-dbc7-4d3e-aabf-59cc5cbd1a1f

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
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
theorem _root_.solution {a : Mat k r} (ha : a ∈ GV k r) : a⁻¹ ∈ GV k r := by
  have hg : aᴴ * Hpk k r * a = Hpk k r := ha
  have hu : IsUnit a.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h1 := congrArg Matrix.det hg
    rw [Matrix.det_mul, h0, mul_zero] at h1
    exact (Hdet k r).ne_zero h1.symm
  have h1 : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
  have h2 : (a⁻¹)ᴴ * aᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [hg]
    _ = ((a⁻¹)ᴴ * aᴴ) * Hpk k r * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
