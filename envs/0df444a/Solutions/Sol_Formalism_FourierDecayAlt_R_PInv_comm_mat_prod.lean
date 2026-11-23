-- Prove2me | solution 1 for Formalism.FourierDecayAlt.R.PInv.comm_mat_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:59.906416+00:00
-- url     : https://prove2.me/submissions/cbeabaf2-3c82-4e04-af86-ece46ba34ebb

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv

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
namespace Formalism.FourierDecayAlt.R.PInv
theorem _root_.solution (x : A) :
    ∀ l : List (Matrix (Fin 2) (Fin 2) A), (∀ M ∈ l, ∀ i j, Commute x (M i j)) →
      ∀ i j, Commute x (l.prod i j)
  | [], _ => by
      intro i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | M :: l, h => by
      intro i j
      rw [List.prod_cons, Matrix.mul_apply]
      exact Commute.sum_right _ _ _ fun k _ =>
        (h M (by simp) i k).mul_right (solution x l (fun N hN => h N (by simp [hN])) k j)
end Formalism.FourierDecayAlt.R.PInv
