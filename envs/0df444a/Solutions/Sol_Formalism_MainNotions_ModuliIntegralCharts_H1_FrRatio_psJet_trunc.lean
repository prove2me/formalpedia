-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio.psJet_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:28.870808+00:00
-- url     : https://prove2.me/submissions/1be06e5d-687a-4615-9e55-f09eaf6ea4a2

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFixAsm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrRatio
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_psTrunc_succ_sub


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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
theorem _root_.solution {S κ : Type} [CommRing S] [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S) :
    (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m) (psJet (m + 1) f) = psJet m f := by
  show Ideal.Quotient.mk _ (psTrunc (m + 1) f) = Ideal.Quotient.mk _ (psTrunc m f)
  exact Ideal.Quotient.eq.2 (psTrunc_succ_sub f)
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
