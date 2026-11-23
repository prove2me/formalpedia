-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.wchart_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:52.072897+00:00
-- url     : https://prove2.me/submissions/f72b1745-4d09-4d3f-94e4-b992b42c9f97

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf

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
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) : (⊤ : Y.Opens) ≤ ⨆ j, LB.wchart L φ j := by
  intro y _
  have hk : ∀ k, ∃ i, (φ k).base y ∈ L.U i := fun k => by
    have hy : (φ k).base y ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using hy
  choose j hj using hk
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩
  show y ∈ ⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X)
  exact Set.mem_iInter.2 fun k => hj k
end Formalism.MainNotions.ModuliIntegralCharts.H1
