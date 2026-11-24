-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.scaled_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:51.471928+00:00
-- url     : https://prove2.me/submissions/6a48a2e1-8708-4cb1-8246-935e1e79247e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqH
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_pullUnit_res

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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
variable {X Y Z : Scheme.{0}} (L : LB X)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
theorem _root_.solution {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) {u : Γ(Y, ⊤)ˣ}
    {t t' : LB.Gen (LB.LinComb L φ ε)} (hs : IsScaled u t t') :
    IsScaled (pullUnit h u) (LB.pullGen L φ ε t h) (LB.pullGen L φ ε t' h) := by
  have hs' : ∀ j, t'.s j = res le_top u * t.s j := hs
  intro j
  simp only [LB.pullGen]
  erw [hs' j, map_mul, map_mul, pullUnit_res]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
