-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.form_mulOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:36:09.936262+00:00
-- url     : https://prove2.me/submissions/97abce79-1681-41cc-8a5d-b72fcb444680

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Theorems.Thm_Formalism_FourierDecayAlt_P5_act_io
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pairAt_mulOp
import Theorems.Thm_Formalism_FourierDecayAlt_P5_glue_succ_update

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
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (u y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    form μ l.succ (act (io (mkP Wv Wv')) u) y (Function.update c l t) =
      fsv s t * form μ l.succ u y (Function.update c l t) := by
  unfold form
  have h : ∀ (c' : Cf r l.succ) (a : Ix S), pairAt μ (act (io (mkP Wv Wv')) u a) (y a) (glue l.succ (Function.update c l t) c') =
      fsv s t * pairAt μ (u a) (y a) (glue l.succ (Function.update c l t) c') := by
    intro c' a
    rw [act_io]
    have e : (mkP Wv Wv' : Pr (RadSp k r z z' π π')).1 = Wv := rfl
    rw [e, pairAt_mulOp μ l s Wv hW, glue_succ_update]
  simp_rw [h, ← Finset.mul_sum, mul_left_comm _ (fsv s t)]
  exact MeasureTheory.integral_const_mul _ _
end Formalism.FourierDecayAlt.P5
