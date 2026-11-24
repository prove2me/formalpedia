-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.coeff_aeval_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:06:56.832706+00:00
-- url     : https://prove2.me/submissions/c8d83261-c15b-4344-a59d-cc913d7d0c6e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_aeval_scale_monomial

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
variable [Fintype ι] [DecidableEq ι]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
theorem _root_.solution (s : ι → R) (p : MvPolynomial ι R) (e : ι →₀ ℕ) :
    coeff e (aeval (fun i => C (s i) * X i) p) = (e.prod fun i k => s i ^ k) * coeff e p := by
  induction p using MvPolynomial.induction_on' with
  | monomial e' a =>
    rw [aeval_scale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      ring
    · simp
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
