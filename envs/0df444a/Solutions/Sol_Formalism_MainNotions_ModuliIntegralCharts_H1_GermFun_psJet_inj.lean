-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.psJet_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:06.139301+00:00
-- url     : https://prove2.me/submissions/b7db9b4b-4855-4410-b983-91ad06f10ae4

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFun
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_coeff_eq_zero_of_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_coeff_psTrunc

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
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
theorem _root_.solution {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] {f f' : MvPowerSeries ι R}
    (h : ∀ m, psJet m f = psJet m f') : f = f' := by
  ext e
  have h0 := h e.degree
  unfold psJet at h0
  have h1 := Ideal.Quotient.eq.1 h0
  have h2 := coeff_eq_zero_of_mem h1 (e := e) (Nat.lt_succ_self _)
  rw [MvPolynomial.coeff_sub, coeff_psTrunc e.degree f e le_rfl,
    coeff_psTrunc e.degree f' e le_rfl] at h2
  exact sub_eq_zero.1 h2
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
