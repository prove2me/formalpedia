-- Prove2me | solution 1 for Formalism.FourierDecayAlt.R.LevelData.inv_comm_Tvprod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:00.712659+00:00
-- url     : https://prove2.me/submissions/f5b43d2f-0c34-4675-9333-22ad3f2abc30

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
theorem _root_.solution {x : A} (hp : ∀ l, Commute x (L.pb l)) (hc : ∀ l, Commute x (L.cb l))
    (hci : ∀ l, Commute x (L.cbi l)) (Y : ℂ) (i j) : Commute x (L.Tvprod Y i j) := by
  apply comm_mat_prod
  intro M hM
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hM)
  intro i j
  fin_cases i <;> fin_cases j <;> simp [LevelData.Tvl, hc l, hci l]
  exact Commute.sub_right (Algebra.commute_algebraMap_right Y x) (hp l)
end _root_.Formalism.FourierDecayAlt.R.LevelData
end Formalism.FourierDecayAlt.R.PInv
