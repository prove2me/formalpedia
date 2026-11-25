-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.psJet_coe_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:23:56.435493+00:00
-- url     : https://prove2.me/submissions/4e7ec26b-af98-4441-b119-4d34cd8695f9

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_EvalSinglePointId
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (g : MvPowerSeries κ S) :
    psJet m ((psTrunc m g : MvPolynomial κ S) : MvPowerSeries κ S) = psJet m g := by
  unfold Formalism.L2.Pj.psJet
  congr 1
  unfold Formalism.L2.Pj.psTrunc
  refine Finset.sum_congr rfl fun e he => ?_
  congr 1
  rw [MvPolynomial.coeff_coe]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd he h
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
