-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.germLargeT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:48:00.342602+00:00
-- url     : https://prove2.me/submissions/2512412e-f145-4d8f-821c-0980cd154dfa

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_norm_orbM_ge
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_detM_orbM
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_K_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_tailBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_coef_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_detM_longM
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_norm_omLong_le
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_OrbitTailEstimates_pow_arith__8930bfb03f06
import Theorems.Thm_Formalism_FourierDecayAlt_P_additive_character_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_root_set_characterization


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitTailEstimates
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.OrbitTailEstimates
theorem _root_.solution : GermLargeT := by
  intro m β Kc hKc h0 t₀ ht₀
  obtain ⟨CT, hCT⟩ := tailBound m β
  obtain ⟨r0, hr0, hr0'⟩ : ∃ r0 : ℝ, 0 < r0 ∧ ∀ D ∈ Kc, r0 ≤ ‖D‖ := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hKc.isClosed.isOpen_compl 0 h0
    refine ⟨ε, hε, fun D hD => ?_⟩
    by_contra hlt
    exact hball (by simpa using not_le.1 hlt : D ∈ Metric.ball (0 : ℂ) ε) hD
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, ∀ D ∈ Kc, ‖D‖ ≤ R0 := hKc.isBounded.exists_norm_le
  set r : ℝ := min 1 r0 with hr
  set R : ℝ := max 1 R0 with hR
  have hrpos : 0 < r := lt_min one_pos hr0
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_left _ _)
  set C1 : ℝ := ∫ v : UT (m + 1 + 1) → ℂ,
      (max 1 ‖r • v‖) ^ (-(((m : ℝ) + 1) * ((m : ℝ) + 4) + 1)) ∂(muPi β (UT (m + 1 + 1))) with hC1
  have hC1pos : 0 ≤ C1 := integral_nonneg fun v => by positivity
  refine ⟨CT * (t₀ ^ (3 * m + 4))⁻¹ + ((m : ℝ) + 2) * R ^ ((m + 1) ^ 2) * C1 / t₀, ?_⟩
  intro V _ _ _ Φ A K hA hΦ t c ht hD
  have ht0 : 0 < ‖t‖ := ht₀.trans_le ht
  have htne : t ≠ 0 := norm_pos_iff.1 ht0
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hbZ : ∀ Z : Mat (m + 1 + 1), detM Z = (wMat (m + 1)).det * (c * t ^ (m + 1)) →
      ‖Φ Z‖ ≤ K * min 1 (‖Z‖ ^ (-A)) := by
    intro Z hZ
    have h3 := (hΦ Z ⟨c * t ^ (m + 1), hD, hZ.symm⟩).2 0 le_rfl
    rwa [norm_iteratedFDeriv_zero] at h3
  have hΦ1 : DerivBound 0 {(wMat (m + 1)).det * (c * t ^ (m + 1))} (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ :=
    fun Z hZ => hΦ Z ⟨c * t ^ (m + 1), hD, (Set.mem_singleton_iff.1 hZ).symm⟩
  have hK : 0 ≤ K := K_nonneg (ht0.trans_le (norm_orbM_ge m t c 0)) (norm_nonneg _)
    (hbZ _ (detM_orbM (m + 1) t c 0))

  have hOm := hCT V Φ A K ‖t‖ t c hA ht0 htne hΦ1
    (fun p hp => absurd hp (not_lt.2 (norm_orbM_ge m t c p)))
  have hCK : 0 ≤ CT * K := by
    rw [mul_assoc] at hOm
    exact coef_nonneg (norm_nonneg _) (by positivity) hOm
  have hfirst : ‖((‖t‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) • OmBlock β (m + 1) Φ t c‖ ≤
      CT * (t₀ ^ (3 * m + 4))⁻¹ * K * ‖t‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hle1 : (max 1 ‖t‖) ^ (((m : ℝ) + 1) * ((m : ℝ) + 4) - A) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by linarith)
    have hinv : (‖t‖ ^ (3 * m + 4))⁻¹ ≤ (t₀ ^ (3 * m + 4))⁻¹ :=
      inv_anti₀ (pow_pos ht₀ _) (pow_le_pow_left₀ ht₀.le ht _)
    calc ‖t‖ ^ ((m + 1) ^ 2) * ‖OmBlock β (m + 1) Φ t c‖
        ≤ ‖t‖ ^ ((m + 1) ^ 2) * (CT * K * (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ *
            (max 1 ‖t‖) ^ (((m : ℝ) + 1) * ((m : ℝ) + 4) - A)) := mul_le_mul_of_nonneg_left hOm (by positivity)
      _ ≤ ‖t‖ ^ ((m + 1) ^ 2) * (CT * K * (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle1 (by positivity)) (by positivity)
      _ = CT * K * (‖t‖ ^ ((m + 1) ^ 2) * (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹) := by ring
      _ = CT * K * (‖t‖ * (‖t‖ ^ (3 * m + 4))⁻¹) := by rw [pow_arith' m _ ht0]
      _ ≤ CT * K * (‖t‖ * (t₀ ^ (3 * m + 4))⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv ht0.le) hCK
      _ = _ := by ring

  have hroot : ∀ z ∈ rootSet (m + 2) ((-1) ^ (m + 3) * (c * t ^ (m + 1))),
      ‖(((‖z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * 1 * psi β (((m : ℂ) + 2) * z / t)) • OmLong β (m + 1) Φ z‖ ≤
        R ^ ((m + 1) ^ 2) * (K * C1) := by
    intro z hz
    have hz' : z ^ (m + 2) = (-1) ^ (m + 3) * (c * t ^ (m + 1)) :=
      ((root_set_characterization (m + 2) _ (by omega)).1 z).1 hz
    have hnz : ‖z‖ ^ (m + 2) = ‖c * t ^ (m + 1)‖ := by
      rw [← norm_pow, hz', norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hzr : r ≤ ‖z‖ := by
      by_contra hlt
      have h1 : ‖z‖ < r := not_le.1 hlt
      have h2 : ‖z‖ ≤ 1 := h1.le.trans (min_le_left _ _)
      have h3 : ‖z‖ ^ (m + 2) ≤ ‖z‖ := pow_le_of_le_one (norm_nonneg _) h2 (by omega)
      have h4 := hr0' _ hD
      have h5 : r ≤ r0 := min_le_right _ _
      linarith
    have hzR : ‖z‖ ≤ R := by
      by_contra hlt
      have h1 : R < ‖z‖ := not_le.1 hlt
      have h2 : 1 ≤ ‖z‖ := (le_max_left _ _).trans h1.le
      have h3 : ‖z‖ ≤ ‖z‖ ^ (m + 2) := le_self_pow₀ h2 (by omega)
      have h4 := hR0 _ hD
      have h5 : R0 ≤ R := le_max_right _ _
      linarith
    rw [norm_smul, norm_mul, norm_mul, (additive_character_psi β _ 0).2.1, norm_one, mul_one, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzR _) ?_ (norm_nonneg _) (by positivity)
    exact norm_omLong_le m β r hrpos Φ A K hA hK z hzr fun v => hbZ _ (detM_longM m z _ hz' v)
  have hcard : ((rootSet (m + 2) ((-1) ^ (m + 3) * (c * t ^ (m + 1)))).card : ℝ) ≤ (m : ℝ) + 2 := by
    have h1 : (rootSet (m + 2) ((-1) ^ (m + 3) * (c * t ^ (m + 1)))).card ≤ m + 2 :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
    exact_mod_cast h1
  have hinv1 : ‖((m : ℂ) + 2)⁻¹‖ ≤ 1 := by
    have e : ((m : ℂ) + 2) = ((m + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [norm_inv, e, Complex.norm_natCast]
    refine inv_le_one_of_one_le₀ ?_
    push_cast; linarith
  have hmain : ‖mainTerm β m (fun _ => 1) Φ t (c * t ^ (m + 1))‖ ≤
      ((m : ℝ) + 2) * R ^ ((m + 1) ^ 2) * C1 / t₀ * K * ‖t‖ := by
    unfold mainTerm
    have hB : 0 ≤ R ^ ((m + 1) ^ 2) * (K * C1) := by positivity
    calc _ ≤ 1 * (((m : ℝ) + 2) * (R ^ ((m + 1) ^ 2) * (K * C1))) := by
          rw [norm_smul]
          refine mul_le_mul hinv1 ?_ (norm_nonneg _) zero_le_one
          refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hroot).trans ?_)
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hcard hB
      _ = ((m : ℝ) + 2) * R ^ ((m + 1) ^ 2) * C1 * K * 1 := by ring
      _ ≤ ((m : ℝ) + 2) * R ^ ((m + 1) ^ 2) * C1 * K * (‖t‖ / t₀) :=
          mul_le_mul_of_nonneg_left ((one_le_div ht₀).2 ht) (by positivity)
      _ = _ := by ring
  unfold remainder
  calc _ ≤ ‖((‖t‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) • OmBlock β (m + 1) Φ t c‖ +
        ‖mainTerm β m (fun _ => 1) Φ t (c * t ^ (m + 1))‖ := norm_sub_le _ _
    _ ≤ CT * (t₀ ^ (3 * m + 4))⁻¹ * K * ‖t‖ + ((m : ℝ) + 2) * R ^ ((m + 1) ^ 2) * C1 / t₀ * K * ‖t‖ :=
        add_le_add hfirst hmain
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
