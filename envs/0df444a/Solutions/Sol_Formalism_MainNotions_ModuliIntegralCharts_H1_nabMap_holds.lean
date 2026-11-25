-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.nabMap_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:43:52.314541+00:00
-- url     : https://prove2.me/submissions/144b2ba8-6f56-425b-863d-e3b3b7142194

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_map_nsmul__ee4e35b9e155
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_map_DpolyOf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_map_expS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_hid
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_map_hL
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_const_hL

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CIndBCNab
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution : NabMapSt := by
  intro S S' _ _ _ _ ψ d O _ _ B B' hF hA h hh w0 m f κ _ u P
  have hc : constantCoeff ((m : S) • B.hL S h w0) = 0 := by
    simp [MvPowerSeries.smul_eq_C_mul, const_hL B h hh w0]
  have hFK : (fun j => MvPowerSeries.map ψ (B.FK S j)) = B'.FK S' := by
    funext j
    simp [FB.FK, FGLaw.mapF, hF, hid]
  simp only [FB.nabVal]
  rw [← MvPowerSeries.constantCoeff_map, map_DpolyOf, map_mul, map_expS ψ _ hc, map_nsmul',
    map_hL ψ B B' hA, hFK]
end Formalism.MainNotions.ModuliIntegralCharts.H1
