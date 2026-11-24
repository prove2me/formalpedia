-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.psJet_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:32:35.409982+00:00
-- url     : https://prove2.me/submissions/b4884d0a-8758-45ca-8c7f-74c015544067

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_psJet_eq_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_coeff_psTrunc


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
theorem _root_.solution (m : ℕ) (f g : MvPowerSeries ι R) : psJet m (f * g) = psJet m f * psJet m g := by
  have key : psJet m (f * g) = Ideal.Quotient.mk _ (psTrunc m f * psTrunc m g) := by
    refine psJet_eq_mk m _ _ (fun e he => ?_)
    rw [MvPolynomial.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hd : x.1.degree + x.2.degree ≤ m := by
      rw [← map_add Finsupp.degree, hx']
      exact he
    rw [GermFun.coeff_psTrunc m f x.1 (by omega), GermFun.coeff_psTrunc m g x.2 (by omega)]
  rw [key, map_mul]
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
