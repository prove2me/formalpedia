-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.ub_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:36.1367+00:00
-- url     : https://prove2.me/submissions/c4764eb6-74e3-4ba7-bed6-07de7dc59e95

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
section defs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma Dw_cons_const_eq_zero (c : E) (x : Bool × Mat k r) (w : List (Bool × Mat k r)) :
    Dw (x :: w) (fun _ : Mat k r => c) = fun _ => 0 := by
  induction w generalizing x with
  | nil =>
    funext g
    show Dx x (fun _ => c) g = 0
    rw [Dx_eq]
    exact deriv_const _ _
  | cons y w ih =>
    show Dx x (Dw (y :: w) fun _ => c) = fun _ => 0
    rw [ih]
    exact Dx_zero x
end defs
section app
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
end app
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution (c : E) (S : Set (Mat k r)) (hSG : S ⊆ GV k r) (n : ℕ) (γ : ℕ) :
    UB (fun _ : Mat k r => c) S n ‖c‖ 0 γ := by
  intro w _ g hg
  have h0 : 0 ≤ gN g := (gN_pos (hSG hg)).le
  cases w with
  | nil =>
    show ‖c‖ ≤ ‖c‖ * gN g ^ (0 + γ * 0)
    simp
  | cons x w =>
    rw [Dw_cons_const_eq_zero]
    simp only [norm_zero]
    exact mul_nonneg (norm_nonneg c) (pow_nonneg h0 _)
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
