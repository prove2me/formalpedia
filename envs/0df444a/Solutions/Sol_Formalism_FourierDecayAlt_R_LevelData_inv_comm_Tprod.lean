-- Prove2me | solution 1 for Formalism.FourierDecayAlt.R.LevelData.inv_comm_Tprod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:00.565981+00:00
-- url     : https://prove2.me/submissions/471801ec-6ee3-445d-b6fd-ba4057764c08

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv
import Theorems.Thm_Formalism_FourierDecayAlt_R_PInv_comm_mat_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.PInv
open Matrix LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.R.PInv
namespace _root_.Formalism.FourierDecayAlt.R.LevelData
theorem _root_.solution {x : A} (hp : ∀ l, Commute x (L.p l)) (hc : ∀ l, Commute x (L.c l))
    (hci : ∀ l, Commute x (L.ci l)) (Y : ℂ) (i j) : Commute x (L.Tprod Y i j) := by
  apply comm_mat_prod
  intro M hM
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hM)
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [LevelData.Tl, (hp l).add_left, Algebra.commutes, hc l, hci l, Commute.neg_right,
      Commute.add_right, Commute.zero_right]
  exact Commute.add_right (Algebra.commute_algebraMap_right Y x) (hp l)
end _root_.Formalism.FourierDecayAlt.R.LevelData
end Formalism.FourierDecayAlt.R.PInv
