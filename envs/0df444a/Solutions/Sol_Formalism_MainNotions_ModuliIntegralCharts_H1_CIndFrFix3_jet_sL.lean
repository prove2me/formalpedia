-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.jet_sL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:30:46.517623+00:00
-- url     : https://prove2.me/submissions/9d11fdf9-b975-4309-8ba8-dd4e24b6067a

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_EvalSinglePointId
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_eval_single_point_id
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_mk_trunc_coe
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_subst
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psTrunc_eq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_power_series_in_fin_one
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_cc_psTrunc__670d9e4bd30f
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
theorem _root_.solution (m : ℕ) (act : Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (hact : ∀ j, MvPowerSeries.constantCoeff (act j) = 0) (f : PS S 2 d) :
    GermD.sL m act (psJet m f) = psJet m (ev (n := 1) ![pt S (n := 1) d 0, comp1 act (pt S (n := 1) d 0)] f) := by
  set P : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S := fun p =>
    (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (act j)] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2 with hPdef
  have hsL : GermD.sL m act = jetSubstP m P := rfl
  have hP : ∀ p, MvPolynomial.constantCoeff (P p) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i
    · simp [hPdef]
    · show MvPolynomial.constantCoeff (psIn d m ![0] (act j)) = 0
      rw [GermD.power_series_in_fin_one, ExpGB.cc_psTrunc']
      exact hact j
  have ha : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((![pt S (n := 1) d 0, comp1 act (pt S (n := 1) d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i
    · simp [pt]
    · show MvPowerSeries.constantCoeff (comp1 act (pt S (n := 1) d 0) j) = 0
      unfold comp1
      rw [eval_single_point_id]
      exact hact j
  rw [hsL]
  unfold ev
  rw [FBIdJet.psJet_subst m _ ha f]
  apply DFunLike.congr_fun
  refine GermD.jet_hom_ext fun p => ?_
  rw [jetSubstP, GermD.jetMap_mk, GermD.jetMap_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X, hP p, map_zero,
    sub_zero]
  obtain ⟨i, j⟩ := p
  fin_cases i
  · show Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)) = psJet m (pt S (n := 1) d 0 j)
    rw [show pt S (n := 1) d 0 j = ((MvPolynomial.X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin d) S) :
      MvPowerSeries (Fin 1 × Fin d) S) from (MvPolynomial.coe_X _).symm, psJet, FBIdJet.psTrunc_eq,
      FBIdJet.mk_trunc_coe]
  · show Ideal.Quotient.mk _ (psIn d m ![0] (act j)) = psJet m (comp1 act (pt S (n := 1) d 0) j)
    rw [GermD.power_series_in_fin_one]
    unfold comp1
    rw [eval_single_point_id]
    rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
