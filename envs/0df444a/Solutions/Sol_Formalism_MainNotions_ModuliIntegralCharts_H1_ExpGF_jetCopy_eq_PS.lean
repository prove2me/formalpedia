-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF.jetCopy_eq_PS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:44:17.79965+00:00
-- url     : https://prove2.me/submissions/50e8e71d-f02f-49cf-b2e9-e69b2f62f375

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ESecToUnit
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSEqJetMap
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_psJet_coe
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_jetSubstPS_X
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk


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
theorem _root_.solution {d n : ℕ} (m : ℕ) (i : Fin n) :
    jetCopy (S := S) d m i =
      jetSubstPS (m := m) (fun p : Fin 1 × Fin d => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin n × Fin d) S)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro p
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_X m _ (fun p => MvPowerSeries.constantCoeff_X _) p, ← MvPolynomial.coe_X, psJet_coe]
  unfold jetCopy
  rw [jetMap_mk, MvPolynomial.aeval_X]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF
