-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.power_series_in_fin_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:47.273952+00:00
-- url     : https://prove2.me/submissions/247aa0e9-5c5b-4e3c-8f01-ccce52c0760e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet

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
theorem _root_.solution (m : ℕ) (g : MvPowerSeries (Fin 1 × Fin d) R) : psIn d m ![0] g = psTrunc m g := by
  unfold psIn
  have h : (fun p : Fin 1 × Fin d => ((![0] : Fin 1 → Fin 1) p.1, p.2)) = id := by
    funext p
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [h]
  simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
