-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.pull_restrict_unit_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:06:47.959231+00:00
-- url     : https://prove2.me/submissions/e4983cf4-8611-4c24-87c0-4227c767b946

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_pull_res_val
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_res_res

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
open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution {X Y : Scheme.{0}} (h : Y ⟶ X) {V : X.Opens} {W W' : Y.Opens} (hWV : W ≤ h ⁻¹ᵁ V)
    (hW' : W' ≤ W) (u : Γ(X, ⊤)ˣ) :
    ((res hW' (res hWV (pullU h V (res (le_top : V ≤ ⊤) u))) : Γ(Y, W')ˣ) : Γ(Y, W')) =
      (Y.presheaf.map (homOfLE (le_top : W' ≤ h ⁻¹ᵁ ⊤)).op).hom ((h.app ⊤).hom (u : Γ(X, ⊤))) := by
  rw [res_res, pull_res_val]
end Formalism.MainNotions.ModuliIntegralCharts.H1
