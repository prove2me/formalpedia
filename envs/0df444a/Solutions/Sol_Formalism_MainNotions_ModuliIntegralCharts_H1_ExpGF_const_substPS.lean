-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF.const_substPS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:47.310195+00:00
-- url     : https://prove2.me/submissions/b5d5a3f4-da72-49cd-99fc-beb4a347cb53

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ESecToUnit
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSEqJetMap

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
variable {S : Type} [CommRing S] {κ κ' κ'' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
  [Fintype κ''] [DecidableEq κ'']
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF
theorem _root_.solution (Q : κ' → MvPowerSeries κ'' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : MvPowerSeries κ' S) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst Q f) = 0 := by
  exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hQ) hQ hf
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF
