-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.opL_dir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:06.214078+00:00
-- url     : https://prove2.me/submissions/57267477-8c77-4c61-8251-6e0a5de958c1

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_fderiv_dir

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
theorem _root_.solution (a : Fin r) (j : Fin 6) {f₁ f₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (κ : ℂ)
    (h1 : DifferentiableAt ℝ f₁ c) (h2 : DifferentiableAt ℝ f₂ c)
    (hev : ∀ᶠ s in 𝓝 (c a), f₁ (Function.update c a s) = κ • f₂ (Function.update c a s)) :
    opL a j f₁ c = κ • opL a j f₂ c := by
  have h0 : f₁ c = κ • f₂ c := by simpa using hev.self_of_nhds
  have hfd := fderiv_dir a κ h1 h2 hev
  fin_cases j
  · show pOp a f₁ c = κ • pOp a f₂ c
    unfold pOp wirt
    split_ifs
    · simp only [hfd, smul_sub, smul_comm κ]
    · simp
  · show c a • f₁ c = κ • (c a • f₂ c)
    rw [h0, smul_comm]
  · show (c a)⁻¹ • f₁ c = κ • ((c a)⁻¹ • f₂ c)
    rw [h0, smul_comm]
  · show pbOp a f₁ c = κ • pbOp a f₂ c
    unfold pbOp wirtBar
    split_ifs
    · simp only [hfd, smul_add, smul_comm κ]
    · simp
  · show star (c a) • f₁ c = κ • (star (c a) • f₂ c)
    rw [h0, smul_comm]
  · show (star (c a))⁻¹ • f₁ c = κ • ((star (c a))⁻¹ • f₂ c)
    rw [h0, smul_comm]
end Formalism.FourierDecayAlt.P.Qx6
