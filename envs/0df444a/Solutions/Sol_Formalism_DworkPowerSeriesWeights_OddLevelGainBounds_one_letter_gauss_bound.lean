-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.one_letter_gauss_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:00:33.431805+00:00
-- url     : https://prove2.me/submissions/a666e713-a5bf-47de-910e-10804d3e944c

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitFamily
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_one_letter_unramified_bound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_minor_monomial_exponent_le
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_logb_max_one_const
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_degree_plain
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_map_oneLog
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_cc_of_noLow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_integral_map
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_admissibleTransfer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bddAbove_norm_coeff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_minorProd_mem_opInt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_intCast_padicComplex
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_residuallyGenericExists
import Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_OneGauss_eval__frameJetOne_ed424e11227c
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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
open OneGauss
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution : OneLetterGauss7 := by
  intro l _ N0 N1 C hl3 K0 hK0 ζ hζ be hbe ep hep g hg0 hg U hU sgn hsgn p hp I n
  have hlp : l.Prime := Fact.out
  obtain ⟨K, instK, hult, hchar, φ, Y, hφ, hgauss, hgen⟩ :=
    residuallyGenericExists l (Fin N0 × Fin N0)
  have := hult
  have := hchar
  have hnl : ‖(l : K)‖ = ‖(l : ℂ_[l])‖ := by rw [← map_natCast φ, hφ]
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by
    have h := norm_intCast_padicComplex l (l : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast] at h
    rw [h]
    exact Padic.norm_p_lt_one
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 (by exact_mod_cast hlp.ne_zero)
  have hY : ∀ y, ‖Y y‖ ≤ 1 := by
    intro y
    have h := hgauss (MvPolynomial.X y)
    rw [MvPolynomial.eval₂_X] at h
    rw [h]
    refine ciSup_le fun m => ?_
    classical
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp
  obtain ⟨hT1, hT2, -, -⟩ := admissibleTransfer ℂ_[l] K φ hφ l 2 N0 N1 K0 ζ be
  have hcc : MvPowerSeries.constantCoeff be = 0 := Transfer.cc_of_noLow hbe.2.2.1
  have hg0' : ∀ y, MvPowerSeries.constantCoeff (MvPowerSeries.map φ (g y)) = 0 := fun y => by
    rw [MvPowerSeries.constantCoeff_map, hg0 y, map_zero]
  have hg' : ∀ y, MvPowerSeries.subst (fun y' => MvPowerSeries.map φ (g y'))
      (oneLog (K := K) l y) = MvPowerSeries.X y := by
    intro y
    have h := congrArg (MvPowerSeries.map φ) (hg y)
    rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hg0), map_oneLog,
      MvPowerSeries.map_X] at h
    exact h
  have hR := one_letter_unramified_bound.{0, 0} K l N0 N1 hlp (hlp.odd_of_ne_two (by omega)) (hnl ▸ hl1)
    (K0.map φ) (hT1 hK0) (φ ζ) (hζ.map_of_injective φ.injective) _ (hT2 hbe) (φ ep)
    (by rw [hφ, hep]) (Fin N0 × Fin N1) (fun x i => frA Y i x)
    (fun x i => by
      unfold frA
      split_ifs
      · exact hY _
      · simp)
    _ hg0' hg' _ (Transfer.integral_map φ hφ hU) (φ sgn) (by rcases hsgn with rfl | rfl <;> simp)
  refine le_trans (le_ciSup (bddAbove_norm_coeff _) n) ?_
  rw [← hgauss, eval₂_frameJetOne φ g hg0 U sgn ep be hcc p hp I Y]
  unfold jetPair
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hl0.le _)
    fun κ hκ => ?_
  have hdeg := degree_plain p hp I κ hκ
  have hint : ‖MvPolynomial.coeff κ (minorProd (fun (i : Fin N0) (b : Fin N1) =>
      (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K)) p hp I)‖ ≤ 1 := by
    refine minorProd_mem_opInt _ (fun i b m => ?_) p hp I κ
    classical
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp
  rw [mul_assoc, norm_mul]
  refine le_trans (mul_le_of_le_one_left (norm_nonneg _) hint) ?_
  refine le_of_le_of_eq (hR κ (max 1 C) (le_max_left _ _)
    (fun y => le_trans (minor_monomial_exponent_le p hp I κ hκ y) (le_max_right _ _))) ?_
  rw [hnl, hdeg, logb_max_one_const]
  simp
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
