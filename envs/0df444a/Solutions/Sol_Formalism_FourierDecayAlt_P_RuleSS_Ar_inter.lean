-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.Ar_inter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:27.340053+00:00
-- url     : https://prove2.me/submissions/e0893fab-2578-4744-a883-6c3f3ebb76dc

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
    (hp : ∀ l, (algebraMap ℂ A Y + L.p l) * h = h * (algebraMap ℂ A Y' + L.p l))
    (hc : ∀ l, L.c l * h = h * L.c l) (hci : ∀ l, L.ci l * h = h * L.ci l) :
    L.Ar Y * h = h * L.Ar Y' ∧ L.Br Y * h = h * L.Br Y' := by
  have key : L.Tprod Y * diagonal (fun _ : Fin 2 => h) = diagonal (fun _ => h) * L.Tprod Y' := by
    unfold LevelData.Tprod
    apply rev_prod_inter
    intro l
    ext i j
    rw [mul_diagonal, diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp [LevelData.Tl, hp l, hc l, hci l]
  have k00 := congrFun (congrFun key 0) 0
  have k10 := congrFun (congrFun key 1) 0
  rw [mul_diagonal, diagonal_mul] at k00 k10
  exact ⟨k00, k10⟩
end Formalism.FourierDecayAlt.P.RuleSS
