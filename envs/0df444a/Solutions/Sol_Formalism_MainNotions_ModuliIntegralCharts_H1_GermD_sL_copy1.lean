-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.sL_copy1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:47:58.973619+00:00
-- url     : https://prove2.me/submissions/5ab5874d-aa0a-47b8-82be-d73968c40476

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_power_series_in_fin_one

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open AlgebraicGeometry CategoryTheory MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
theorem _root_.solution (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    (sL m g).comp (jetCopy d m (1 : Fin 2)) = jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (g p.2) := by
  apply jet_hom_ext
  rintro ⟨i1, j⟩
  obtain rfl : i1 = 0 := Subsingleton.elim _ _
  simp [sL, jetSubstP, jetCopy, jetMap_mk, power_series_in_fin_one]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
