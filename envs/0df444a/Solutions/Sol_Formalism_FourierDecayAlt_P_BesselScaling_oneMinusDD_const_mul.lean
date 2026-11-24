-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BesselScaling.oneMinusDD_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:33:53.488067+00:00
-- url     : https://prove2.me/submissions/62f7a20d-af03-48c7-b7e1-032f3e41461e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselScaling
import Theorems.Thm_Formalism_FourierDecayAlt_P_BesselScaling_iteratedDeriv_two_const_mul

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
namespace Formalism.FourierDecayAlt.P.BesselScaling
theorem _root_.solution (c : ℂ) (h : ℝ → ℝ → ℂ) (t₁ t₂ : ℝ) :
    oneMinusDD (fun a b => c * h a b) t₁ t₂ = c * oneMinusDD h t₁ t₂ := by
  simp only [oneMinusDD, iteratedDeriv_two_const_mul, ← mul_sub]
end Formalism.FourierDecayAlt.P.BesselScaling
