-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.subG_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:19:53.23248+00:00
-- url     : https://prove2.me/submissions/e2f52fe7-f2e9-49ae-9bc8-2b8f4748f455

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
theorem _root_.solution (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) :
    subG r tau gm plc (MvPolynomial.X y) = ∑ col, MvPolynomial.C (Gm r tau gm (eW r tau N y).1 col (eW r tau N y).2) *
      MvPolynomial.X (lam r tau plc ((eW r tau N y).1, col)) := by
  unfold subG
  rw [MvPolynomial.aeval_X]
  rfl
end Formalism.L2.FormalSeriesBounds.RF
