-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.lin_add_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:48:02.480743+00:00
-- url     : https://prove2.me/submissions/26eda623-4413-4c82-b63d-6770d1cc755d

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
variable [Algebra ℚ S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
theorem _root_.solution (A Ab : Fin d → Fin d → S) (hAA : ∀ i l, A i l + Ab i l = if i = l then 1 else 0) {n : ℕ}
    (k : Fin n) : (fun i => lin A k i + lin Ab k i) = xs S d k := by
  funext i
  simp only [lin, xs, ← Finset.sum_add_distrib, ← add_mul, ← map_add, hAA]
  simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
