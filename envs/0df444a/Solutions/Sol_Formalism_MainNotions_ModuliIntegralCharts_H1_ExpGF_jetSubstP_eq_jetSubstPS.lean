-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF.jetSubstP_eq_jetSubstPS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:42.835371+00:00
-- url     : https://prove2.me/submissions/3aaede38-16a0-436b-a327-6ee3c1ab16a6

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
theorem _root_.solution (m : ℕ) (σ : κ → MvPolynomial κ' S) (hσ : ∀ i, MvPolynomial.constantCoeff (σ i) = 0) :
    jetSubstP m σ = jetSubstPS (m := m) (fun i => (σ i : MvPowerSeries κ' S)) := by
  have hσ' : ∀ i, MvPowerSeries.constantCoeff ((σ i : MvPowerSeries κ' S)) = 0 := fun i => by
    show MvPowerSeries.coeff (0 : κ' →₀ ℕ) ((σ i : MvPowerSeries κ' S)) = 0
    rw [MvPolynomial.coeff_coe]
    exact hσ i
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_X m _ hσ' i, psJet_coe]
  unfold jetSubstP
  rw [jetMap_mk, MvPolynomial.aeval_X, hσ i, map_zero, sub_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF
