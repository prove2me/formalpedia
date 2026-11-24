-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BesselScaling.betaInf_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:11:53.378443+00:00
-- url     : https://prove2.me/submissions/00761470-418c-40e7-9b3f-8401a43c5599

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselScaling
import Theorems.Thm_Formalism_FourierDecayAlt_P_BesselScaling_oneMinusDD_const_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BesselScaling_ph_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_oneMinusDD_const_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BesselScaling
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
variable [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BesselScaling
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) :
    betaInf (scaleG D c hc) F F' = ((c : ℝ) : ℂ) * betaInf D F F' := by
  have hreg : ∀ p, regBracket (scaleG D c hc) F F' p =
      fun a b => ((c : ℝ) : ℂ) * regBracket D F F' p a b := by
    intro p
    funext a b
    have hχ : (scaleG D c hc).χ = D.χ := rfl
    simp only [regBracket]
    rw [ph_scale, hχ]
    ring
  have hz : (scaleG D c hc).z = D.z := rfl
  have hz' : (scaleG D c hc).z' = D.z' := rfl
  have hS : (scaleG D c hc).μSS = D.μSS := rfl
  unfold betaInf betaInfTau
  simp only [hreg, hz, hz', hS, oneMinusDD_const_mul, mul_assoc, integral_const_mul]
  rw [← integral_const_mul]
  congr 1
  funext p
  ring
end Formalism.FourierDecayAlt.P.BesselScaling
