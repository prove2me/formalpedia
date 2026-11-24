-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.monomial_mem_orig_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:46:55.092674+00:00
-- url     : https://prove2.me/submissions/7a45f0c6-2229-4fea-a30c-72908070b24d

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB

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
theorem _root_.solution (e : ι →₀ ℕ) (a : R) : monomial e a ∈ orig R ι ^ e.degree := by
  rw [monomial_eq]
  apply Ideal.mul_mem_left
  unfold Finsupp.prod
  have hpow : orig R ι ^ e.degree = ∏ i ∈ e.support, orig R ι ^ e i := by
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hpow]
  exact Ideal.prod_mem_prod (fun i _ => Ideal.pow_mem_pow (show (X i : MvPolynomial ι R) ∈ orig R ι from Ideal.subset_span (Set.mem_range_self i)) _)
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
