-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.mem_orig_pow_of_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:44.279176+00:00
-- url     : https://prove2.me/submissions/38757435-9a46-489a-875e-a867f6f0fa84

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_monomial_mem_orig_pow

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPolynomial Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
variable {R ι : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
theorem _root_.solution (n : ℕ) (p : MvPolynomial ι R) (h : ∀ e, e.degree < n → coeff e p = 0) :
    p ∈ orig R ι ^ n := by
  rw [p.as_sum]
  refine Ideal.sum_mem _ (fun e he => ?_)
  have hn : n ≤ e.degree := by
    by_contra hlt
    push_neg at hlt
    exact (mem_support_iff.mp he) (h e hlt)
  exact Ideal.pow_le_pow_right hn (monomial_mem_orig_pow e _)
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
