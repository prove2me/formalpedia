-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.snd_tp_psJet_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:40:51.359177+00:00
-- url     : https://prove2.me/submissions/54f8daf6-4f8b-4fe0-ba4f-78a51b7b53d0

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_tp_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_tp_comp_jetMap
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_subst


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
theorem _root_.solution {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (h : κ' → R)
    (a : κ → MvPowerSeries κ' R) (ha : ∀ p, MvPowerSeries.constantCoeff (a p) = 0) (f : MvPowerSeries κ R) :
    (tp h (psJet (0 + 1) (MvPowerSeries.subst a f))).snd =
      ∑ p, (∑ q, h q * MvPowerSeries.coeff (Finsupp.single q 1) (a p)) *
        MvPowerSeries.coeff (Finsupp.single p 1) f := by
  rw [psJet_subst (0 + 1) a ha f, ← AlgHom.comp_apply, tp_comp_jetMap h a ha, tp_psJet]
  simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
