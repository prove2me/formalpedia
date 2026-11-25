-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.triangle_inequality_at_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:57:44.613117+00:00
-- url     : https://prove2.me/submissions/faeeb09b-7b0d-4f28-a069-069977a0f116

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Tri_hsVec_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Tri_hsVec_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Tri_Ew_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Tri_cs_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.FourierDecayAlt.P.TBBx2.Tri
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TBB.TriAt := by
  intro Wp Wq _ _ _ _ _ _ P p f n fi a b C₁ C₄ n₀ p₀ γ Qγ hb ha hj hB hγ hG hQ
  have hb0 : 0 < b := by linarith
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ,
      S = Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hA0 : 0 ≤ ∑ i, ‖a i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (a i))
  have hEf : Ew p (fun _ => 1) f (P.r + 1) [] γ = S * ‖B.hsVec (p.V f γ)‖ ^ 2 := by rw [hSdef]; exact Ew_top p f hγ
  have hEi : ∀ i, Ew p (fun _ => 1) (fi i) (P.r + 1) [] γ = S * ‖B.hsVec (p.V (fi i) γ)‖ ^ 2 := fun i => by
    rw [hSdef]; exact Ew_top p (fi i) hγ
  have hEi0 : ∀ i, 0 ≤ Ew p (fun _ => 1) (fi i) (P.r + 1) [] γ := fun i => by
    rw [hEi i]; exact mul_nonneg hS0 (sq_nonneg _)
  have hvec : (Qγ : ℂ) • B.hsVec (p.V f γ) = ∑ i, a i • B.hsVec (p.V (fi i) γ) := by
    rw [← hsVec_smul, hQ, hsVec_sum]
    simp only [hsVec_smul]
  have hnorm : ‖Qγ‖ * ‖B.hsVec (p.V f γ)‖ ≤ ∑ i, ‖a i‖ * ‖B.hsVec (p.V (fi i) γ)‖ := by
    have h1 := congrArg norm hvec
    rw [norm_smul, Complex.norm_real] at h1
    rw [h1]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_smul (a i) _).le)
  have hcs := cs_bound (fun i => ‖a i‖) (fun i => ‖B.hsVec (p.V (fi i) γ)‖) (fun i => norm_nonneg (a i))
  have hQ2 : Qγ ^ 2 * ‖B.hsVec (p.V f γ)‖ ^ 2 ≤ (∑ i, ‖a i‖) * ∑ i, ‖a i‖ * ‖B.hsVec (p.V (fi i) γ)‖ ^ 2 := by
    have h0 : 0 ≤ ‖Qγ‖ * ‖B.hsVec (p.V f γ)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc Qγ ^ 2 * ‖B.hsVec (p.V f γ)‖ ^ 2 = (‖Qγ‖ * ‖B.hsVec (p.V f γ)‖) ^ 2 := by
          rw [mul_pow, Real.norm_eq_abs, sq_abs]
      _ ≤ (∑ i, ‖a i‖ * ‖B.hsVec (p.V (fi i) γ)‖) ^ 2 := pow_le_pow_left₀ h0 hnorm 2
      _ ≤ _ := hcs
  have hreal : Qγ ^ 2 * Ew p (fun _ => 1) f (P.r + 1) [] γ ≤ (∑ i, ‖a i‖) * ∑ i, ‖a i‖ * Ew p (fun _ => 1) (fi i) (P.r + 1) [] γ := by
    rw [hEf]
    simp only [hEi]
    have h2 := mul_le_mul_of_nonneg_left hQ2 hS0
    have e3 : ∑ i, ‖a i‖ * (S * ‖B.hsVec (p.V (fi i) γ)‖ ^ 2) = S * ∑ i, ‖a i‖ * ‖B.hsVec (p.V (fi i) γ)‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e3]
    nlinarith [h2]
  have hstep : ∀ i, ENNReal.ofReal (Ew p (fun _ => 1) (fi i) (P.r + 1) [] γ) ≤ ENNReal.ofReal (b ^ (C₄ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) * jN2 p f := fun i =>
    (hB i γ hγ hG).trans (by gcongr; exact hj i)
  calc ENNReal.ofReal (Qγ ^ 2 * Ew p (fun _ => 1) f (P.r + 1) [] γ)
      ≤ ENNReal.ofReal ((∑ i, ‖a i‖) * ∑ i, ‖a i‖ * Ew p (fun _ => 1) (fi i) (P.r + 1) [] γ) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (∑ i, ‖a i‖) * ∑ i, ENNReal.ofReal ‖a i‖ * ENNReal.ofReal (Ew p (fun _ => 1) (fi i) (P.r + 1) [] γ) := by
        rw [ENNReal.ofReal_mul hA0,
          ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hEi0 i))]
        congr 1
        exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_mul (norm_nonneg _)
    _ ≤ ENNReal.ofReal (∑ i, ‖a i‖) * ∑ i, ENNReal.ofReal ‖a i‖ * (ENNReal.ofReal (b ^ (C₄ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) * jN2 p f) := by
        gcongr with i hi
        exact hstep i
    _ = ENNReal.ofReal (∑ i, ‖a i‖) * ENNReal.ofReal (∑ i, ‖a i‖) * ENNReal.ofReal (b ^ (C₄ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) * jN2 p f := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg (a i))]
        ring
    _ ≤ ENNReal.ofReal (b ^ ((2 * C₁ + C₄) * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) * jN2 p f := by
        gcongr ?_ * _
        rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul (mul_nonneg hA0 hA0)]
        apply ENNReal.ofReal_le_ofReal
        have hU : b ^ (C₁ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * b ^ (C₁ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * b ^ (C₄ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) = b ^ ((2 * C₁ + C₄) * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) := by
          rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]
          congr 1
          ring
        calc (∑ i, ‖a i‖) * (∑ i, ‖a i‖) * (b ^ (C₄ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀))
            ≤ b ^ (C₁ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * b ^ (C₁ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (b ^ (C₄ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) := by gcongr
          _ = b ^ ((2 * C₁ + C₄) * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀) := by rw [← hU]; ring
end Formalism.FourierDecayAlt.P
