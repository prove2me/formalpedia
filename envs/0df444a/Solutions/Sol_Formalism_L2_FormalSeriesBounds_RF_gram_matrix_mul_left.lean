-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.gram_matrix_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:50.129329+00:00
-- url     : https://prove2.me/submissions/3292e472-c95c-41db-8fec-85633154984f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_gram_matrix_mul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] (r : T → ℕ) (tau : Orb → ZMod 2 → T)
  (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
variable {r tau}
variable (r tau)
variable {r tau gm}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (α : AA r tau N) (col col' : Fin 2) : ∑ g, Gm r tau gm α col' g * Mm r tau gm α col g = if col' = col then 1 else 0 := by
  have hAB : (Matrix.of fun g col => Mm r tau gm α col g) * (Matrix.of fun col g => Gm r tau gm α col g) = 1 := by
    ext g' g
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact gram_matrix_mul_right gm_hyp α g g'
  have hBA := mul_eq_one_comm.1 hAB
  have := congrFun (congrFun hBA col') col
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this
end Formalism.L2.FormalSeriesBounds.RF
