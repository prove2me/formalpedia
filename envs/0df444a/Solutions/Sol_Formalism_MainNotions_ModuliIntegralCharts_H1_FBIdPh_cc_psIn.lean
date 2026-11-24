-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.cc_psIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:41.419805+00:00
-- url     : https://prove2.me/submissions/2b8e15a1-f4bb-4be5-b34a-2fbb2034f712

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdPh_cc_aeval
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdPh_cc_psTrunc

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] (d : ℕ)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
theorem _root_.solution {n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : PS S n d) :
    constantCoeff (psIn d m r f) = MvPowerSeries.constantCoeff f := by
  unfold psIn
  first
    | (rw [MvPolynomial.constantCoeff_rename]; exact cc_psTrunc m f)
    | simp [cc_psTrunc]
    | (rw [show (rename fun p : Fin n × Fin d => (r p.1, p.2)) (psTrunc m f) =
          aeval (fun p : Fin n × Fin d => (X (r p.1, p.2) : MvPolynomial (Fin n' × Fin d) S)) (psTrunc m f) from
          DFunLike.congr_fun (MvPolynomial.algHom_ext fun i => by simp) _]
       rw [cc_aeval _ (fun p => by simp)]
       exact cc_psTrunc m f)
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
