-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.prod_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:39:53.001346+00:00
-- url     : https://prove2.me/submissions/f3116afe-7dea-44bf-ade8-3157349dc9e3

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_tm_inter

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
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b)
    (l : List (ℂ × Fin n × Fin n)) :
    (l.map fun p => Tm E p.1 p.2.1 p.2.2).prod * R = R * (l.map fun p => Tm E' p.1 p.2.1 p.2.2).prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc, ih, ← mul_assoc, tm_inter E E' R h, mul_assoc]
end Formalism.FourierDecayAlt.Q.TInvW
