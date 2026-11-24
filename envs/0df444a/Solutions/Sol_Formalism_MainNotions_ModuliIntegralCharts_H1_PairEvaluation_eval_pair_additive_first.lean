-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.eval_pair_additive_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:48:00.875678+00:00
-- url     : https://prove2.me/submissions/ce7b828c-9eee-4d74-901f-872d71d56a74

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_eval_pair

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
open MvPolynomial
variable {S : Type} [CommRing S] {d : ℕ}
variable [Algebra ℚ S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
theorem _root_.solution {h : MvPolynomial (Fin 2 × Fin d) S}
    (hA : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2))
    {τ : Type} (u u' v : Fin d → MvPolynomial τ S) :
    ev2 h (fun i => u i + u' i) v = ev2 h u v + ev2 h u' v := by
  have := congrArg (aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2)) hA
  rw [map_add, aeval_eval_pair, aeval_eval_pair, aeval_eval_pair] at this
  have e0 : (fun i => aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2) (xs S d (0 : Fin 3) i + xs S d 1 i)) =
      fun i => u i + u' i := by funext i; simp [xs]
  have e1 : (fun i => aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2) (xs S d (0 : Fin 3) i)) = u := by
    funext i; simp [xs]
  have e2 : (fun i => aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2) (xs S d (1 : Fin 3) i)) = u' := by
    funext i; simp [xs]
  have e3 : (fun i => aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2) (xs S d (2 : Fin 3) i)) = v := by
    funext i; simp [xs]
  rw [e0, e1, e2, e3] at this
  exact this
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
