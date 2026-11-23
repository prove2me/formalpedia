-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.tailStepOfBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:52.668113+00:00
-- url     : https://prove2.me/submissions/1b3ee807-0cd1-4b8c-ba75-65f51bfeffa3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_pow_arith

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
theorem _root_.solution : TailStepOfBound := by
  intro hTB hCut hCP m β
  obtain ⟨C1, hC1⟩ := hTB m β
  obtain ⟨C2, hC2⟩ := hCP (m + 1 + 1) 0
  refine ⟨C1 * C2, ?_⟩
  intro V _ _ _ Φ A K ε t c hε hε1 hA ht ht1 hΦ
  have ht0 : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set τ : ℝ := ‖t‖ ^ (-ε) with hτ
  have hτ1 : 1 ≤ τ := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith)
  have hτ0 : 0 < τ := by linarith
  have hD := (hC2 V Φ _ _ τ hτ1 hΦ).2
  have hD' : DerivBound 0 {(wMat (m + 1)).det * (c * t ^ (m + 1))}
      (fun Z => (C2 * K) * min 1 (‖Z‖ ^ (-A))) (cutPhiC τ Φ) := by
    intro Z hZ
    obtain ⟨h1, h2⟩ := hD Z hZ
    refine ⟨h1, fun j hj => ?_⟩
    have h3 : ‖iteratedFDeriv ℝ j (cutPhiC τ Φ) Z‖ ≤ C2 * (K * min 1 (‖Z‖ ^ (-A))) := h2 j hj
    show ‖iteratedFDeriv ℝ j (cutPhiC τ Φ) Z‖ ≤ C2 * K * min 1 (‖Z‖ ^ (-A))
    rwa [mul_assoc]
  have hvan : ∀ p : BlockCoord (m + 1), ‖orbM (m + 1) t c p‖ < τ →
      cutPhiC τ Φ (orbM (m + 1) t c p) = 0 := by
    intro p hp
    unfold cutPhiC
    rw [((hCut (m + 1 + 1)).1 τ _ hτ0).2.2.1 hp.le]
    simp
  have hq : 3 * (m : ℝ) + 4 ≤ (A - ((m : ℝ) + 1) * ((m : ℝ) + 4)) * ε := by
    rw [← div_le_iff₀ hε]; linarith
  have hN : ((m : ℝ) + 1) * ((m : ℝ) + 4) + 1 ≤ A := by
    have h1 : (A - ((m : ℝ) + 1) * ((m : ℝ) + 4)) * ε ≤ A - ((m : ℝ) + 1) * ((m : ℝ) + 4) := by
      have h2 : 0 ≤ A - ((m : ℝ) + 1) * ((m : ℝ) + 4) := by
        have : 0 ≤ (3 * (m : ℝ) + 4) / ε := by positivity
        linarith
      nlinarith
    linarith
  have h := hC1 V (cutPhiC τ Φ) A (C2 * K) τ t c hN hτ0 ht hD' hvan
  rw [max_eq_right hτ1] at h
  have hpow : τ ^ (((m : ℝ) + 1) * ((m : ℝ) + 4) - A) ≤ ‖t‖ ^ (3 * m + 4) := by
    rw [hτ, ← Real.rpow_mul ht0.le, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_ge ht0 ht1 ?_
    push_cast
    linarith
  have hpos : 0 < (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * τ ^ (((m : ℝ) + 1) * ((m : ℝ) + 4) - A) := by positivity
  have hc0 : 0 ≤ C1 * (C2 * K) := by
    by_contra hneg
    have h1 : C1 * (C2 * K) * ((‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * τ ^ (((m : ℝ) + 1) * ((m : ℝ) + 4) - A)) < 0 :=
      mul_neg_of_neg_of_pos (not_le.1 hneg) hpos
    have h2 := norm_nonneg (OmBlock β (m + 1) (cutPhiC τ Φ) t c)
    rw [mul_assoc] at h
    linarith
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc ‖t‖ ^ ((m + 1) ^ 2) * ‖OmBlock β (m + 1) (cutPhiC τ Φ) t c‖
      ≤ ‖t‖ ^ ((m + 1) ^ 2) * (C1 * (C2 * K) * (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ *
          τ ^ (((m : ℝ) + 1) * ((m : ℝ) + 4) - A)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ ‖t‖ ^ ((m + 1) ^ 2) * (C1 * (C2 * K) * (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * ‖t‖ ^ (3 * m + 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
    _ = C1 * (C2 * K) * (‖t‖ ^ ((m + 1) ^ 2) * ((‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * ‖t‖ ^ (3 * m + 4))) := by ring
    _ = C1 * C2 * K * ‖t‖ := by rw [pow_arith m _ ht0]; ring
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
