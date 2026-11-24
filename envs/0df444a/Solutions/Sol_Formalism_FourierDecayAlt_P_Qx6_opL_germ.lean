-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.opL_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:41:02.061465+00:00
-- url     : https://prove2.me/submissions/960dc755-17e7-43be-8db9-6ab3d7f39f36

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (a : Fin r) (j : Fin 6) {f₁ f₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (hev : f₁ =ᶠ[𝓝 c] f₂) :
    opL a j f₁ c = opL a j f₂ c := by
  have h0 : f₁ c = f₂ c := hev.self_of_nhds
  have hfd : fderiv ℝ f₁ c = fderiv ℝ f₂ c := hev.fderiv_eq
  fin_cases j
  · show pOp a f₁ c = pOp a f₂ c
    unfold pOp wirt
    rw [hfd]
  · show c a • f₁ c = c a • f₂ c
    rw [h0]
  · show (c a)⁻¹ • f₁ c = (c a)⁻¹ • f₂ c
    rw [h0]
  · show pbOp a f₁ c = pbOp a f₂ c
    unfold pbOp wirtBar
    rw [hfd]
  · show star (c a) • f₁ c = star (c a) • f₂ c
    rw [h0]
  · show (star (c a))⁻¹ • f₁ c = (star (c a))⁻¹ • f₂ c
    rw [h0]
end Formalism.FourierDecayAlt.P.Qx6
