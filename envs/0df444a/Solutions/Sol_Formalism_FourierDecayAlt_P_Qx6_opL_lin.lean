-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.opL_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:37:55.837815+00:00
-- url     : https://prove2.me/submissions/778b0424-f012-4481-a673-43c059090f4a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add


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
theorem _root_.solution (a : Fin r) (j : Fin 6) {f₁ f₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (s : ℂ)
    (h1 : DifferentiableAt ℝ f₁ c) (h2 : DifferentiableAt ℝ f₂ c) :
    opL a j (fun x => f₁ x + s • f₂ x) c = opL a j f₁ c + s • opL a j f₂ c := by
  have hfd : ∀ v, fderiv ℝ (fun x => f₁ x + s • f₂ x) c v = fderiv ℝ f₁ c v + s • fderiv ℝ f₂ c v := by
    intro v
    have h : HasFDerivAt (fun x => f₁ x + s • f₂ x) (fderiv ℝ f₁ c + s • fderiv ℝ f₂ c) c :=
      h1.hasFDerivAt.add (h2.hasFDerivAt.const_smul s)
    rw [h.fderiv]
    rfl
  fin_cases j
  · show pOp a _ c = pOp a f₁ c + s • pOp a f₂ c
    unfold pOp wirt
    split_ifs
    · simp only [hfd, smul_sub, smul_add, smul_comm s]
      abel
    · simp
  · show c a • (f₁ c + s • f₂ c) = c a • f₁ c + s • (c a • f₂ c)
    rw [smul_add, smul_comm]
  · show (c a)⁻¹ • (f₁ c + s • f₂ c) = (c a)⁻¹ • f₁ c + s • ((c a)⁻¹ • f₂ c)
    rw [smul_add, smul_comm]
  · show pbOp a _ c = pbOp a f₁ c + s • pbOp a f₂ c
    unfold pbOp wirtBar
    split_ifs
    · simp only [hfd, smul_add, smul_comm s]
      abel
    · simp
  · show star (c a) • (f₁ c + s • f₂ c) = star (c a) • f₁ c + s • (star (c a) • f₂ c)
    rw [smul_add, smul_comm]
  · show (star (c a))⁻¹ • (f₁ c + s • f₂ c) = (star (c a))⁻¹ • f₁ c + s • ((star (c a))⁻¹ • f₂ c)
    rw [smul_add, smul_comm]
end Formalism.FourierDecayAlt.P.Qx6
