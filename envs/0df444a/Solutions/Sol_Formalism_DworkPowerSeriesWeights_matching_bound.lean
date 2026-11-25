-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.matching_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:40:45.855751+00:00
-- url     : https://prove2.me/submissions/1dd171bc-1da4-41ff-82f0-f785404c38f5

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementQ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_IntegralOperatorsOnJets
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_integral_operators_on_jets
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_linForm_mem_opInt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_polar_le
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_matching_existence
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
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : MatchBound.{u} := by
  intro K _ _ _ pi hpi0 hpi1 ι _ c S sg n L hc hS hsg hL M hM
  have hB1 : (1 : ℝ) ≤ pi ^ (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpi0 hpi1.le (by norm_num)
  have hB0 : (0 : ℝ) ≤ pi ^ (-(1 / 2 : ℝ)) := zero_le_one.trans hB1
  rw [matching_existence K ι c S sg n L]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hpi0.le _)
    fun σ hσ => ?_
  have hσ2 : σ * σ = 1 := (Finset.mem_filter.mp hσ).2
  by_cases h : ∀ i, i < σ i → polar c (L i) (L (σ i)) ≠ 0
  · have hcard := hM σ hσ2 h
    rw [norm_mul, norm_prod]
    have h1 : (∏ i ∈ Finset.univ.filter (fun i => i < σ i), ‖-S * polar c (L i) (L (σ i))‖) ≤
        (pi ^ (-(1 / 2 : ℝ))) ^ (Finset.univ.filter (fun i => i < σ i)).card := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
      rw [norm_mul, norm_neg]
      calc ‖S‖ * ‖polar c (L i) (L (σ i))‖ ≤ pi ^ (-(1 / 2 : ℝ)) * 1 :=
            mul_le_mul hS (norm_polar_le c hc _ _ (hL i) (hL (σ i))) (norm_nonneg _) hB0
        _ = pi ^ (-(1 / 2 : ℝ)) := mul_one _
    have h2 : (pi ^ (-(1 / 2 : ℝ))) ^ (Finset.univ.filter (fun i => i < σ i)).card ≤
        (pi ^ (-(1 / 2 : ℝ))) ^ M := pow_le_pow_right₀ hB1 hcard
    have h3 : (pi ^ (-(1 / 2 : ℝ))) ^ M = pi ^ (-(1 / 2 : ℝ) * M) := by
      rw [Real.rpow_mul_natCast hpi0.le]
    have h4 : ‖jetPair (∏ i ∈ Finset.univ.filter (fun i => σ i = i), linForm (L i)) sg‖ ≤ 1 := by
      refine integral_operators_on_jets K ι sg hsg _ ?_
      have : (∏ i ∈ Finset.univ.filter (fun i => σ i = i), linForm (L i)) ∈ opInt K ι :=
        Subring.prod_mem _ fun i _ => linForm_mem_opInt (L i) (hL i)
      exact this
    calc _ ≤ pi ^ (-(1 / 2 : ℝ) * M) * 1 :=
          mul_le_mul ((h1.trans h2).trans h3.le) h4 (norm_nonneg _) (Real.rpow_nonneg hpi0.le _)
      _ = _ := mul_one _
  · push Not at h
    obtain ⟨i, hi, h0⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩) (by rw [h0, mul_zero]),
      zero_mul, norm_zero]
    exact Real.rpow_nonneg hpi0.le _
end Formalism.DworkPowerSeriesWeights
