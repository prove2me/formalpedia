-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.prod_position
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:42.747089+00:00
-- url     : https://prove2.me/submissions/a9a8342b-fa7f-4569-b7ea-42939ea316fb

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
theorem _root_.solution (k : Fin 2) (e : Fin 2 × Fin d →₀ ℕ) :
    (e.prod fun p n => (if p.1 = k then (2 : S) else 1) ^ n) = 2 ^ (∑ i, e (k, i)) := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fin.prod_univ_two]
  fin_cases k <;> simp [Finset.prod_pow_eq_pow_sum]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
