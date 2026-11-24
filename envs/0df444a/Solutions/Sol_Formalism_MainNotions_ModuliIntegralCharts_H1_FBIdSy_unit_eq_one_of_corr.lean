-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy.unit_eq_one_of_corr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:46:58.872966+00:00
-- url     : https://prove2.me/submissions/e05ad89f-a1d3-4959-b6b5-f4d2dce61354

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_scaleGenG_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_scale_eq_of_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_refl


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
theorem _root_.solution (hL : t.PP.L.IsLB) {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)}
    {ε : K → ℤ} {g : LB.Gen (LB.LinComb t.PP.L φ ε)} (hg : g.IsGen) {v : Γ(Y, ⊤)ˣ}
    (h : LB.Gen.Corr t.PP.L φ ε φ ε g (scaleGenG t φ ε v g)) : v = 1 := by
  have h1 := FBIdLB.scale_eq_of_corr t hL (DVR.corr_refl _ hg) (v := 1) (v' := v)
    (by rw [FBIdLB.scaleGenG_one]; exact h)
  exact h1.symm
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
