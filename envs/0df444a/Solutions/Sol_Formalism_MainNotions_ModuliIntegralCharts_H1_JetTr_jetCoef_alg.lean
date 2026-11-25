-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.jetCoef_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:34:40.853184+00:00
-- url     : https://prove2.me/submissions/f7fc282d-eea0-47a5-bcf9-362fb3464b0f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartTransportSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_jetCoef_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {V K : Type} [CommRing V] [CommRing K] (f : V →+* K)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
theorem _root_.solution (κ : Type) (m : ℕ) :
    (jetCoef f κ m).comp (algebraMap V (Jet V κ m)) = (algebraMap K (Jet K κ m)).comp f := by
  refine RingHom.ext fun v => ?_
  first
  | (show jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.C v)) = Ideal.Quotient.mk _ (MvPolynomial.C (f v))
     rw [jetCoef_mk, MvPolynomial.map_C])
  | (simp only [RingHom.comp_apply]
     rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq,
       MvPolynomial.algebraMap_eq, jetCoef_mk, MvPolynomial.map_C])
end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
