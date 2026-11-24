-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.left_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:55:24.479571+00:00
-- url     : https://prove2.me/submissions/78524012-a780-4e53-8d66-e19e451549a5

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_tl00
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_tl01
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_tl10
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_tl11

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution (hL : QMinorLeftH) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Y : ℂ) (p q : Fin 2) (F : Mx k r → E) (s g : Mx k r)
    (hy : yv k r z i (s * g) = yv k r z i g) (hyb : ybv k r z i (s * g) = ybv k r z i g) :
    tL k r z z' i Y p q (fun x => F (s * x)) g = tL k r z z' i Y p q F (s * g) := by
  have hq : ∀ {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ),
      qminorOp (EH k r) a b u (fun x => F (s * x)) g = qminorOp (EH k r) a b u F (s * g) := by
    intro t a b u
    exact congrFun (hL E (2 * r + k + 1) t (Hpk k r) F a b u s) g
  match p, q with
  | 0, 0 =>
    rw [tl00, tl00]
    exact hq _ _ _
  | 0, 1 =>
    rw [tl01, tl01]
    simp only [Pi.neg_apply, chatL, hq, hyb]
  | 1, 0 =>
    rw [tl10, tl10]
    simp only [Pi.neg_apply, chatL, hq, hy]
  | 1, 1 =>
    rw [tl11, tl11]
    simp only [Pi.neg_apply, chat2L, hq, hy, hyb]
end Formalism.FourierDecayAlt.Q.TInvW
