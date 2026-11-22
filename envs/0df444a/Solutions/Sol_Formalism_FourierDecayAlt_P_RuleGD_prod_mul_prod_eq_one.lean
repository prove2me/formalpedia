-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.prod_mul_prod_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:10:26.86855+00:00
-- url     : https://prove2.me/submissions/891c1846-9851-48a5-84f3-d1bbf96725a7

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_comm_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleGD
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Matrix
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.RuleGD
theorem _root_.solution {n : ℕ} (f g : Fin n → A) (hfg : ∀ i, f i * g i = 1)
    (hc : ∀ i j, g i * f j = f j * g i) : (List.ofFn f).prod * (List.ofFn g).prod = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have hcomm := (comm_prod (fun i => f i.succ) (g 0) (fun i => hc 0 i.succ)).symm
    rw [mul_assoc, ← mul_assoc _ (g 0), hcomm, ← mul_assoc, ← mul_assoc, hfg 0, one_mul,
      ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hfg i.succ) (fun i j => hc i.succ j.succ)]
end Formalism.FourierDecayAlt.P.RuleGD
