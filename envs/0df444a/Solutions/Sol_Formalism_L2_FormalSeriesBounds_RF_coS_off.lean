-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.coS_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:22:55.546387+00:00
-- url     : https://prove2.me/submissions/df6957fe-62f4-436f-90fc-5ab333d78b6b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjCharts
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_coS_lam
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α : AA r tau N) (col : Fin 2)
    (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) (h : y.1 ≠ α.1) :
    coS r tau gm plc (lam r tau plc (α, col)) y = 0 := by
  have e : y = (eW r tau N).symm ((eW r tau N y).1, (eW r tau N y).2) := by
    rw [Prod.mk.eta, Equiv.symm_apply_apply]
  rw [e, coS_lam plc inj, if_neg]
  intro h2
  apply h
  rw [h2]
  rfl
end Formalism.L2.FormalSeriesBounds.RF
