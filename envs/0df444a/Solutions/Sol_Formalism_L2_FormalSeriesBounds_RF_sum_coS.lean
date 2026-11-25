-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.sum_coS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:26:08.761318+00:00
-- url     : https://prove2.me/submissions/89476cf5-74ee-4b69-9c1a-3734aaa0261a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_coS_lam

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
variable (r tau gm)
variable {r tau gm}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) {M : Type} [AddCommMonoid M]
    (α : AA r tau N) (col : Fin 2) (Φ : C → (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) → M) (h0 : ∀ y, Φ 0 y = 0) :
    ∑ y, Φ (coS r tau gm plc (lam r tau plc (α, col)) y) y =
      ∑ g, Φ (Mm r tau gm α col g) ((eW r tau N).symm (α, g)) := by
  rw [← Equiv.sum_comp (eW r tau N).symm, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single α]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [coS_lam plc inj, if_pos rfl]
  · intro α' _ hne
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [coS_lam plc inj, if_neg (Ne.symm hne), h0]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.L2.FormalSeriesBounds.RF
