-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.jetMap_zR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:07:40.789489+00:00
-- url     : https://prove2.me/submissions/577d4abe-cfdd-4bcb-8607-9442ca75b87c

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ChartSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartDataPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution {S : Type} [CommRing S] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (h) (s : κ) :
    (jetMap φ h : Jet S κ m →ₐ[S] Jet S κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X s)) = Ideal.Quotient.mk _ (φ s) := by
  simp only [jetMap]
  show ((Ideal.Quotient.mkₐ S (orig S κ' ^ (m + 1))).comp (MvPolynomial.bind₁ φ)) (MvPolynomial.X s) = _
  simp
end Formalism.MainNotions.ModuliIntegralCharts.H1
