-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.jetSubstP_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:33:25.33944+00:00
-- url     : https://prove2.me/submissions/6e44e1b0-aeec-4ab0-a31d-d039b6c1b35f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_psJet_eq_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_coeff_aeval_scale
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_jetMap_mk
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
theorem _root_.solution (m : ℕ) (s : ι → R) (f : MvPowerSeries ι R) :
    jetSubstP m (fun i => C (s i) * X i) (psJet m f) = psJet m (MvPowerSeries.rescale s f) := by
  unfold jetSubstP psJet
  rw [jetMap_mk]
  simp only [map_mul, constantCoeff_C, constantCoeff_X, mul_zero, map_zero, sub_zero]
  symm
  refine psJet_eq_mk m _ _ (fun e he => ?_)
  rw [coeff_aeval_scale, GermFun.coeff_psTrunc m f e he, MvPowerSeries.coeff_rescale]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
