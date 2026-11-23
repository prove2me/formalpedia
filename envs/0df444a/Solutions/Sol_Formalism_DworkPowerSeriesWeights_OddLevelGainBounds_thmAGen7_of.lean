-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.thmAGen7_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:47.17571+00:00
-- url     : https://prove2.me/submissions/1b2c402d-f759-4445-b49a-0bdb09df21ef

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_ThmAGen7Of
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_frameM_genA
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_pair_linearity
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_minorProd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_subst_linSub
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_subst_mvExp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_genA_eq_rowOp
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds MvPolynomial
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution (hO : ThmAOp7.{u}) : ThmAGen7.{u} := by
  intro K _ _ _ l d N0 N1 _ hl h3 hd hev hpi h0 K0 hun ζ hζ be hbe x hx g hg0 hg U hU ε hε TT colN
    p hp hp1 I T hT xg hxg nu1 nu2 size hn1 hn2 hsz spec hs1 hs2 hs3
  have key := hO K l d N0 N1 hl h3 hd hev hpi h0 K0 hun ζ hζ be hbe x hx g hg0 hg U hU ε hε
    TT colN p hp hp1 I T hT nu1 nu2 size hn1 hn2 hsz spec hs1 hs2 hs3
  set aa : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K := fun j =>
    ∑ i : ZV d N0 N1, MvPowerSeries.C (genA TT T i j) * MvPowerSeries.X i with haa
  have hs : MvPowerSeries.HasSubst aa :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by simp [haa]
  have hlin : ∀ z, MvPowerSeries.subst aa (linSub (frameM (N1 := N1) x) z) =
      linSub (frameM (N1 := N1) xg) z :=
    subst_linSub _ _ _ (frameM_genA TT T x xg hxg)
  have hlin0 : ∀ z, MvPowerSeries.constantCoeff (linSub (frameM (N1 := N1) x) z) = 0 := by
    intro z
    simp [linSub]
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := by
    by_contra h
    have h' : MvPowerSeries.coeff 0 be ≠ 0 := by
      rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have := (hbe.2.2.1 0 h').1
    simp [degE] at this
  have hbS0 : MvPowerSeries.constantCoeff (bSum (frameM (N1 := N1) x) be) = 0 := by
    unfold bSum
    rw [map_sum]
    refine Finset.sum_eq_zero fun ab _ => ?_
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => hlin0 _) (fun s => hlin0 _) hbe0
  have hbS : MvPowerSeries.subst aa (bSum (frameM (N1 := N1) x) be) =
      bSum (frameM (N1 := N1) xg) be := by
    unfold bSum
    rw [← MvPowerSeries.coe_substAlgHom hs, map_sum]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hs, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => hlin0 _) hs]
    simp only [hlin]
  have hΘ : MvPowerSeries.subst (linSub (frameM (N1 := N1) xg)) (MvPowerSeries.subst g U) *
      mvExp (ε • bSum (frameM (N1 := N1) xg) be) =
      MvPowerSeries.subst aa
        (MvPowerSeries.subst (linSub (frameM (N1 := N1) x)) (MvPowerSeries.subst g U) *
          mvExp (ε • bSum (frameM (N1 := N1) x) be)) := by
    rw [MvPowerSeries.subst_mul hs, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hlin0) hs, subst_mvExp hs _ (by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hbS0, mul_zero]),
      MvPowerSeries.subst_smul hs, hbS]
    simp only [hlin]
  rw [hΘ, jet_pair_linearity K (ZV d N0 N1) (ZV d N0 N1) (genA TT T), map_prod]
  simp only [map_minorProd, MvPolynomial.aeval_X, sum_genA_eq_rowOp]
  exact key
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
