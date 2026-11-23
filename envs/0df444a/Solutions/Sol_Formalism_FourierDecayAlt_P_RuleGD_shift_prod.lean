-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.shift_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:53.058064+00:00
-- url     : https://prove2.me/submissions/b14d1547-53ec-4b61-8efd-35b59b095d33

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD

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
theorem _root_.solution {n : ℕ} (f : Fin n → A) (x : A) (a : Fin n → ℂ)
    (hx : ∀ i, x * f i = f i * x + a i • f i) :
    x * (List.ofFn f).prod = (List.ofFn f).prod * x + (∑ i, a i) • (List.ofFn f).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, ← mul_assoc, hx 0, add_mul, mul_assoc,
      ih (fun i => f i.succ) (fun i => a i.succ) (fun i => hx i.succ)]
    simp only [mul_add, add_smul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    abel
end Formalism.FourierDecayAlt.P.RuleGD
