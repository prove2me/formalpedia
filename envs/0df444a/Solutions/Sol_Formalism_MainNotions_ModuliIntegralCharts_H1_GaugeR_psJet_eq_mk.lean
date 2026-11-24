-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.psJet_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:07.461802+00:00
-- url     : https://prove2.me/submissions/cc4e3a63-d532-45e8-89d6-1099d11ad9dc

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_mem_orig_pow_of_coeff
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
theorem _root_.solution (m : ℕ) (f : MvPowerSeries ι R) (p : MvPolynomial ι R)
    (h : ∀ e, e.degree ≤ m → coeff e p = MvPowerSeries.coeff e f) :
    psJet m f = Ideal.Quotient.mk _ p := by
  unfold psJet
  rw [Ideal.Quotient.eq]
  apply mem_orig_pow_of_coeff
  intro e he
  rw [coeff_sub, GermFun.coeff_psTrunc m f e (by omega), h e (by omega), sub_self]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
