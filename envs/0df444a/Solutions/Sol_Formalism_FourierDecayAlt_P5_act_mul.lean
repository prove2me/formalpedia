-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.act_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:08:59.463019+00:00
-- url     : https://prove2.me/submissions/21b1759b-054d-444e-b4ae-3597605d027b

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_fst_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_fst_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (x : Ix S → RadSp k r z z' π π') :
    act (M * N) x = act M (act N x) := by
  funext a
  simp only [act, Matrix.mul_apply, pr_fst_sum, pr_fst_mul, LinearMap.sum_apply, Module.End.mul_apply,
    map_sum]
  exact Finset.sum_comm
end Formalism.FourierDecayAlt.P5
