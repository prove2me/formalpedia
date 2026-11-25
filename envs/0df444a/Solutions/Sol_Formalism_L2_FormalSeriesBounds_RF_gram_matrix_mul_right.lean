-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.gram_matrix_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:03:52.685652+00:00
-- url     : https://prove2.me/submissions/443e87df-b913-4014-a3e9-cd55659faad7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight

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
    (α : AA r tau N) (g g' : Fin 2) : ∑ col, Mm r tau gm α col g' * Gm r tau gm α col g = if g' = g then 1 else 0 := by
  have h := gm_hyp α.2.1 α.2.2.1 (1 - g') g
  unfold Mm Gm
  rw [h]
  clear h
  fin_cases g <;> fin_cases g' <;> simp
end Formalism.L2.FormalSeriesBounds.RF
