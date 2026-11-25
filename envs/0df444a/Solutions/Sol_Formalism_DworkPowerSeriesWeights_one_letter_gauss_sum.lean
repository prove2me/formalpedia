-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.one_letter_gauss_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:14:22.150527+00:00
-- url     : https://prove2.me/submissions/1ae52c5e-b557-4938-b2f1-766433f5ea40

import Definitions.Def_Formalism_GaussJetBounds_StatementU
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_map_oneLog
import Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_OneGauss_eval__frameJetOne_ed424e11227c
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_degree_plain
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_cc_of_noLow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_integral_map
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_admissibleTransfer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_gauss_sum_powers
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_minorProd_mem_opInt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_intCast_padicComplex
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_oneLetterR
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_residuallyGenericExists


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
open Formalism.IncomingBounds
open OneGauss
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : OneLetterGauss := by
  intro l _ N0 N1 C hl3 K0 hK0 ζ hζ be hbe ep hep g hg hgl U hU sgn hsgn p hp I a ha hpa n
  have hprime : Nat.Prime l := Fact.out
  haveI : Fact (1 < l) := ⟨hprime.one_lt⟩
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by
    have h := norm_intCast_padicComplex l (l : ℤ)
    push_cast at h
    rw [h]
    exact Padic.norm_p_lt_one
  obtain ⟨K, _, _, _, φ, Y, hφ, hY, hgen⟩ := residuallyGenericExists l (Fin N0 × Fin N0)
  have hlK : ‖(l : K)‖ = ‖(l : ℂ_[l])‖ := by rw [← map_natCast φ, hφ]
  have hYn : ∀ y, ‖Y y‖ ≤ 1 := by
    intro y
    have h := hgen (MvPolynomial.X y) (by simp [MvPolynomial.X_ne_zero])
    rw [MvPolynomial.aeval_X] at h
    exact h.le
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := Transfer.cc_of_noLow hbe.2.2.1
  have hG := gauss_sum_powers ℂ_[l] K φ (Fin N0 × Fin N0) Y hY (fun _ => 1) (fun _ => one_ne_zero)
    (frameJetOne p hp I (thetaOne g U sgn ep be)) n
  simp only [pow_one] at hG
  refine hG.trans ?_
  rw [eval₂_frameJetOne φ g hg U sgn ep be hbe0 p hp I Y]
  have TB := admissibleTransfer ℂ_[l] K φ hφ l 2 0 0 K0 ζ be
  have hg' : ∀ x, MvPowerSeries.constantCoeff (MvPowerSeries.map φ (g x)) = 0 := by
    intro x
    simp [hg x]
  have hgl' : ∀ x : Fin N0 × Fin N1, MvPowerSeries.subst (fun y => MvPowerSeries.map φ (g y)) (oneLog (K := K) l x) =
      MvPowerSeries.X x := by
    intro x
    have h := congrArg (MvPowerSeries.map φ) (hgl x)
    rwa [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hg), map_oneLog,
      MvPowerSeries.map_X] at h
  have hsgn' : φ sgn = 1 ∨ φ sgn = -1 := by
    rcases hsgn with h | h
    · left
      simp [h]
    · right
      simp [h]
  have hfrA : ∀ (x : Fin N0 × Fin N1) (i : Fin N0 × Fin N1), ‖frA Y i x‖ ≤ 1 := by
    intro x i
    unfold frA
    split_ifs
    · exact hYn _
    · simp
  have hmin : ∀ κ, ‖MvPolynomial.coeff κ (minorProd (fun (i : Fin N0) (b : Fin N1) =>
      (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K)) p hp I)‖ ≤ 1 := by
    have hm := minorProd_mem_opInt (K := K) (σ := Fin N0 × Fin N1)
      (fun (i : Fin N0) (b : Fin N1) => (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K))
      (fun i b κ => by
        rw [MvPolynomial.coeff_X']
        split_ifs <;> simp) p hp I
    exact hm
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by
    rw [norm_pos_iff]
    exact_mod_cast hprime.ne_zero
  unfold jetPair
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro κ hκ
  have hR := oneLetterR K l N0 N1 hprime (hprime.odd_of_ne_two (by omega)) (hlK ▸ hl1)
    (Subfield.map φ K0) (TB.1 hK0) (φ ζ) (hζ.map_of_injective φ.injective)
    (MvPowerSeries.map φ be) (TB.2.1 hbe) (φ ep) (by rw [hφ, hep]) (Fin N0 × Fin N1)
    (fun x i => frA Y i x) (fun x i => hfrA x i) (fun y => MvPowerSeries.map φ (g y)) hg' hgl'
    (MvPowerSeries.map φ U) (Transfer.integral_map φ hφ hU) (φ sgn) hsgn' κ
  rw [degree_plain p hp I κ hκ, hlK] at hR
  rw [mul_assoc, norm_mul]
  refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (hmin κ)) (le_trans hR ?_)
  apply Real.rpow_le_rpow_of_exponent_ge hlpos hl1.le
  have hcard : ((Fintype.card (Fin N0 × Fin N1) : ℕ) : ℝ) = (N0 : ℝ) * N1 := by simp
  rw [hcard]
  have hlog : Real.logb l (∑ c, p c : ℕ) ≤ Real.logb l a := by
    rcases Nat.eq_zero_or_pos (∑ c, p c) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.logb_zero]
      exact Real.logb_nonneg (by exact_mod_cast hprime.one_lt) (by exact_mod_cast ha)
    · exact Real.logb_le_logb_of_le (by exact_mod_cast hprime.one_lt) (by exact_mod_cast hpos)
        (by exact_mod_cast hpa)
  have hN : (0 : ℝ) ≤ (N0 : ℝ) * N1 := by positivity
  nlinarith
end Formalism.DworkPowerSeriesWeights
