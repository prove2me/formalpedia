-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio.triple_lift_truncation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:37:42.802373+00:00
-- url     : https://prove2.me/submissions/f3e38417-83c3-4ef4-952f-884587cb5ea2

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFixAsm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrRatio
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_jpt_tr

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
theorem _root_.solution (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) (i j k : Fin 3) :
    (ρn x0 d 3 m).left ≫ (lift (jptG t x0 d x (m + 1) i) (lift (jptG t x0 d x (m + 1) j) (jptG t x0 d x (m + 1) k))).left =
      (lift (jptG t x0 d x m i) (lift (jptG t x0 d x m j) (jptG t x0 d x m k))).left := by
  unfold ρn
  rw [← Over.comp_left]
  simp only [comp_lift, jpt_tr hch]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
