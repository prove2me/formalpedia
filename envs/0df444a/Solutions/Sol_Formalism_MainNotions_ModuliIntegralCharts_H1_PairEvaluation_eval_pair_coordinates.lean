-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.eval_pair_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:48:01.79494+00:00
-- url     : https://prove2.me/submissions/22676841-782a-4951-a768-416d27fbcb0d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
theorem _root_.solution (h : MvPolynomial (Fin 2 × Fin d) S) : ev2 h (xs S d 0) (xs S d 1) = h := by
  have hf : (fun p : Fin 2 × Fin d => ![xs S d 0, xs S d 1] p.1 p.2) = X := by
    funext p
    rcases p with ⟨k, i⟩
    fin_cases k <;> simp [xs]
  unfold ev2
  rw [hf, aeval_X_left_apply]
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
