-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf.exists_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:41.267808+00:00
-- url     : https://prove2.me/submissions/bcb52660-8d45-4a8d-a448-707c4753d914

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartPrimTrSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartFrameTrA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartPrimTrPfA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ChartPrimTrPf_corr_self

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {X Y : Scheme.{0}} {K : Type} [Fintype K]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
theorem _root_.solution (L : LB X) {φ φ' : K → (Y ⟶ X)} (h : φ' = φ) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen) :
    ∃ c' : LB.Gen (LB.LinComb L φ' ε), c'.IsGen ∧ LB.Gen.Corr L φ' ε φ ε c' c := by
  subst h
  exact ⟨c, hc, corr_self L _ ε c⟩
end Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
