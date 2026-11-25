-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.theorem_B_gauss_sums
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:07:17.962141+00:00
-- url     : https://prove2.me/submissions/84dc2fa1-6be5-4b3b-b3e9-acd9c39372b8

import Definitions.Def_Formalism_GaussJetBounds_StatementY
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GaussB
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_GaussB_norm_det_generic
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_GaussB_cc_expo
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_GaussB_map_expo
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_GaussB_jetsIntegral_map
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bddAbove_norm_coeff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_mvExp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_intCast_padicComplex
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_residuallyGenericExists
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ringMap_minorProd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_theorem_B
import Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_eval__jetPairPoly_5113198bcf9c
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
open Formalism Formalism.DworkPowerSeriesWeights
open GaussB
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : ThmBGauss := by
  intro p _ H _ _ N0 N1 S u hS hu sg hsg TT colN ht hht hht1 I nu1 nu2 size hnu1 hnu2 hsize n
  have hpp : p.Prime := Fact.out
  obtain ⟨K, instK, hult, hchar, φ, Y, hφ, hgauss, hgen⟩ :=
    residuallyGenericExists p ((Bool × H) × Fin N0 × Fin N0)
  have := hult
  have := hchar
  have hnp : ‖(p : K)‖ = ‖(p : ℂ_[p])‖ := by rw [← map_natCast φ, hφ]
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := by
    have h := norm_intCast_padicComplex p (p : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast] at h
    rw [h]
    exact Padic.norm_p_lt_one
  have hp0 : 0 < ‖(p : ℂ_[p])‖ := norm_pos_iff.2 (by exact_mod_cast hpp.ne_zero)
  have hY : ∀ y, ‖Y y‖ ≤ 1 := by
    intro y
    have h := hgauss (MvPolynomial.X y)
    rw [MvPolynomial.eval₂_X] at h
    rw [h]
    refine ciSup_le fun m => ?_
    classical
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp
  have hB := theorem_B.{0} K ‖(p : ℂ_[p])‖ hp0 hp1 H N0 N1 (φ S) (fun t => φ (u t))
    (by rw [hφ]; exact hS) (fun t => by rw [hφ]; exact hu t) _ (jetsIntegral_map φ hφ hsg)
    (fun τ => Matrix.of fun i a : Fin N0 => Y (τ, i, a)) (fun τ i a => hY _)
    (fun τ => norm_det_generic p Y hgen τ) TT colN ht hht hht1 I nu1 nu2 size hnu1 hnu2 hsize
  refine le_trans (le_ciSup (bddAbove_norm_coeff _) n) ?_
  rw [← hgauss, eval₂_jetPairPoly, map_mul, map_mvExp φ _ (cc_expo S u), map_expo, map_prod]
  simp only [ringMap_minorProd, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
  exact hB
end Formalism.DworkPowerSeriesWeights
