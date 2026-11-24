-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:55:38.570234+00:00
-- url     : https://prove2.me/submissions/fc982e3f-0d09-4966-a005-147db61586af

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_REAL_hasDerivAt_matrix_exp_smul_at_zero
import Theorems.Thm_Formalism_REAL_hasDerivAt_mul_exp_smul_zero


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
theorem _root_.solution (x : Bool × Mat k r) (g : Mat k r) : HasDerivAt (crv x g) (dirv x g) 0 := by
  rcases x with ⟨_ | _, X⟩
  · exact hasDerivAt_mul_exp_smul_zero g X
  · have h := (mulRightRealCLM g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_matrix_exp_smul_at_zero (-X))
    have e : (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * g) =
        (mulRightRealCLM g) ∘ fun t : ℝ => NormedSpace.exp ((t : ℂ) • -X) := by
      funext t
      simp only [Function.comp_apply, smul_neg]
      rfl
    show HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * g) (-X * g) 0
    rw [e]
    exact h
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
