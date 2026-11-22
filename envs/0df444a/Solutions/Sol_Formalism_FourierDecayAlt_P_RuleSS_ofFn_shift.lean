-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.ofFn_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:55:28.031087+00:00
-- url     : https://prove2.me/submissions/5a850a55-03aa-464f-beb1-a03c5bfdf337

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.RuleSS
theorem _root_.solution (x : A) :
    ∀ (n : ℕ) (f : Fin n → A) (k : Fin n → ℂ), (∀ m, x * f m = f m * (x + algebraMap ℂ A (k m))) →
      x * (List.ofFn f).prod = (List.ofFn f).prod * (x + algebraMap ℂ A (∑ m, k m))
  | 0, _, _, _ => by simp
  | n + 1, f, k, h => by
      have ih := solution x n (fun i => f i.succ) (fun i => k i.succ) (fun i => h i.succ)
      rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, map_add]
      set P := (List.ofFn fun i => f i.succ).prod
      calc x * (f 0 * P) = (x * f 0) * P := by noncomm_ring
        _ = f 0 * (x * P + algebraMap ℂ A (k 0) * P) := by rw [h 0]; noncomm_ring
        _ = f 0 * (P * (x + algebraMap ℂ A (∑ i : Fin n, k i.succ)) + P * algebraMap ℂ A (k 0)) := by
            rw [ih, Algebra.commutes]
        _ = _ := by noncomm_ring
end Formalism.FourierDecayAlt.P.RuleSS
