-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.tp_psJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:04.082695+00:00
-- url     : https://prove2.me/submissions/4dcf59f7-c4e9-4e98-abdf-8a3f074ac085

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_aeval_inr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psTrunc_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
private lemma coeff_psTrunc_lemma {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R)
    (e : κ →₀ ℕ) (he : e.degree < 0 + 1 + 1) :
    MvPolynomial.coeff e (psTrunc (0 + 1) f) = MvPowerSeries.coeff e f := by
  rw [psTrunc_eq, MvPowerSeries.coeff_truncTotal _ he]
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (g : κ → R) (f : MvPowerSeries κ R) :
    tp g (psJet (0 + 1) f) = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff f) +
      TrivSqZeroExt.inr (∑ q, g q * MvPowerSeries.coeff (Finsupp.single q 1) f) := by
  have h1 : tp g (psJet (0 + 1) f) =
      MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) (psTrunc (0 + 1) f) := rfl
  rw [h1, aeval_inr, coeff_psTrunc_lemma f 0 (by simp [Finsupp.degree]),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  congr 2
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [coeff_psTrunc_lemma f _ (by simp [Finsupp.degree_single])]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
