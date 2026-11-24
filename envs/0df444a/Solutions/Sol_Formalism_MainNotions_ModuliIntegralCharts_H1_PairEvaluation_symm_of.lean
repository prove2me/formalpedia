-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.symm_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:48:03.258916+00:00
-- url     : https://prove2.me/submissions/44a8afa1-ee95-4001-9b1f-7adf57ff7793

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
theorem _root_.solution {h : MvPolynomial (Fin 2 × Fin d) S} (hs : ev2 h (xs S d 1) (xs S d 0) = h) {τ : Type}
    (u v : Fin d → MvPolynomial τ S) : ev2 h u v = ev2 h v u := by
  have := aeval_eval_pair (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) h (xs S d 1) (xs S d 0)
  rw [hs] at this
  change aeval (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) h = _
  rw [this]
  congr 1 <;> funext i <;> simp [xs]
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
