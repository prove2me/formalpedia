-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.aeval_diag_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:41:45.010802+00:00
-- url     : https://prove2.me/submissions/dd835f09-192d-4c5d-8035-65c56c824340

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
theorem _root_.solution {σ : Type} (s : σ → S) (e : σ →₀ ℕ) (a : S) :
    aeval (fun p => C (s p) * X p) (monomial e a) = monomial e ((e.prod fun p k => s p ^ k) * a) := by
  rw [aeval_monomial, algebraMap_eq, monomial_eq, C_mul]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  ring
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
