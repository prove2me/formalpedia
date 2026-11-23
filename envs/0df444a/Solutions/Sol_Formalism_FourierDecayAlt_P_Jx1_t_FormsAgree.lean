-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx1.t_FormsAgree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:19.732041+00:00
-- url     : https://prove2.me/submissions/d7e2d82f-47f0-434c-8b38-95d62dfddc9b

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_t_TowersAgree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1
namespace Formalism.FourierDecayAlt.P.Jx1
theorem _root_.solution : FormsAgree := by
  unfold FormsAgree
  intro E W _ _ D H _ _ Φ T ε i w hw hg
  unfold TB.Data.Q TB.Data.Sf TA.Slev TA.gram
  rw [t_TowersAgree E T i]
  set X := TA.PT (fun j s => T.Sg (j - s + 1) s) i with hX
  have hS : (∑ p ∈ X, ∑ q ∈ X, D.Kr i p q * D.gram ε i w p q) =
      (D.wt w : ℂ) * ∑ p ∈ X, ∑ p' ∈ X, (toTA D).K i p p' * inner ℂ (Φ w p) (Φ w p') := by
    rw [Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hg]
    simp only [toTA]
    ring
  rw [hS, Complex.re_ofReal_mul]
  first
  | exact mul_div_cancel_left₀ _ hw
  | field_simp
end Formalism.FourierDecayAlt.P.Jx1
