-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.coeff_eq_of_psJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:30:42.45132+00:00
-- url     : https://prove2.me/submissions/fec0450b-883b-479f-9608-b2abad0717dd

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {D : ℕ} {a b : MvPowerSeries ι R}
    (h : psJet D a = psJet D b) {e : ι →₀ ℕ} (he : e.degree ≤ D) :
    MvPowerSeries.coeff e a = MvPowerSeries.coeff e b := by
  have h' : Ideal.Quotient.mk (orig R ι ^ (D + 1)) (psTrunc D a) =
      Ideal.Quotient.mk (orig R ι ^ (D + 1)) (psTrunc D b) := h
  have hm := Ideal.Quotient.eq.mp h'
  have h0 := coeff_eq_zero_of_mem hm (show e.degree < D + 1 by omega)
  rw [MvPolynomial.coeff_sub, coeff_psTrunc D a e he, coeff_psTrunc D b e he] at h0
  exact sub_eq_zero.mp h0
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
