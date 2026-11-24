-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.ptSec_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:52.947751+00:00
-- url     : https://prove2.me/submissions/3bef77ed-c8ac-41d8-b242-481296a2a57e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jBase_trunc

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
variable {t x0 d x}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
theorem _root_.solution (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) :
    (ptSecT t.G (x m)).left ≫ (jBaseG x0 d m 1 ▷ t.G).left =
      (ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left ≫ (jBaseG x0 d (m + 1) 1 ▷ t.G).left := by
  unfold ptSecT
  rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left]
  congr 1
  simp only [lift_whiskerRight, comp_lift, Category.id_comp, jBase_trunc]
  rw [show ρT x0 d m ≫ x (m + 1) = x m from hch.trunc m]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
