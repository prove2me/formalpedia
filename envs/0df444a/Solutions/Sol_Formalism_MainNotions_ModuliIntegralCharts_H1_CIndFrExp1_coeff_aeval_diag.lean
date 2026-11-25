-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.coeff_aeval_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:36.70858+00:00
-- url     : https://prove2.me/submissions/49b2654c-5932-4bc2-82ec-7aef443014c0

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp1_aeval_diag_monomial

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
theorem _root_.solution {σ : Type} (s : σ → S) (h : MvPolynomial σ S) (e : σ →₀ ℕ) :
    coeff e (aeval (fun p => C (s p) * X p) h) = (e.prod fun p k => s p ^ k) * coeff e h := by
  classical
  conv_lhs => rw [h.as_sum]
  rw [map_sum, coeff_sum]
  simp only [aeval_diag_monomial, coeff_monomial]
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb]
  · intro he
    simp only [MvPolynomial.mem_support_iff, not_not] at he
    rw [if_pos rfl, he, mul_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
