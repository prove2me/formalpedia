-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.Avr_inter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:27.768013+00:00
-- url     : https://prove2.me/submissions/fa80d7ef-33f6-414f-b7e9-43b07dfdac31

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_rev_prod_inter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.P.RuleSS
theorem _root_.solution (h : A) (Y Y' : ℂ)
    (hp : ∀ l, (algebraMap ℂ A Y - L.pb l) * h = h * (algebraMap ℂ A Y' - L.pb l))
    (hc : ∀ l, L.cb l * h = h * L.cb l) (hci : ∀ l, L.cbi l * h = h * L.cbi l) :
    L.Avr Y * h = h * L.Avr Y' ∧ L.Bvr Y * h = h * L.Bvr Y' := by
  have key : L.Tvprod Y * diagonal (fun _ : Fin 2 => h) = diagonal (fun _ => h) * L.Tvprod Y' := by
    unfold LevelData.Tvprod
    apply rev_prod_inter
    intro l
    ext i j
    rw [mul_diagonal, diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp [LevelData.Tvl, hp l, hc l, hci l]
  have k00 := congrFun (congrFun key 0) 0
  have k10 := congrFun (congrFun key 1) 0
  rw [mul_diagonal, diagonal_mul] at k00 k10
  exact ⟨k00, k10⟩
end Formalism.FourierDecayAlt.P.RuleSS
