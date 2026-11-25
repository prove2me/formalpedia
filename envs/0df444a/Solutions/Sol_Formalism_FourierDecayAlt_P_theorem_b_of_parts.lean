-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.theorem_b_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:51:00.908615+00:00
-- url     : https://prove2.me/submissions/b79511ac-33f4-48b6-9224-7f626996876f

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Bp_const_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Bp_jacobi_norm_sq_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB MeasureTheory
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TBB.ThmBpOfParts := by
  intro C₃ CΛ C₀ C₂ Cκ hC₃ hCΛ hC₀ hC₂
  refine ⟨40 + CΛ + max 0 (Real.log C₂ / Real.log 3) + |Cκ| + 2 * C₃ * (3 * C₀ + 10), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f Fp Fm b Λ κ₀ n₀ p₀ hb hΛ hΛb hκ hκb hT hn₀ hp₀ hN hPp hPm hR γ hγ hG
  have hb0 : 0 < b := by linarith
  have hT0 : 0 < Tq p := by linarith
  have hX0 : 0 ≤ (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) := by positivity
  have hK0 : 0 ≤ κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) := by positivity
  have hTn0 : 0 ≤ (Tq p)⁻¹ ^ n₀ := by positivity
  have hBq0 : 0 ≤ b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) := by positivity
  have hZ0 : 0 ≤ κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) := mul_nonneg (mul_nonneg hK0 hTn0) hBq0
  have hD := hR (2 * p₀ + n₀) le_rfl
  have hFb : ∀ F, F ∈ ({Fp, Fm} : Set (B.Mat P.k P.r → (Wq →L[ℂ] Wp))) →
      PtBound p F (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) →
      ENNReal.ofReal (Ew p (fun _ => 1) F (P.r + 1) [] γ) ≤ ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) * jN2 p f := by
    intro F hF hP
    have hj := Formalism.FourierDecayAlt.P.TBBx2.Bp.jacobi_norm_sq_bound p f F n₀ p₀ hT (fun c => hN.2 c F hF)
    calc ENNReal.ofReal (Ew p (fun _ => 1) F (P.r + 1) [] γ)
        ≤ ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) * jN2 p F := hP γ hγ hG
      _ ≤ ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) * (ENNReal.ofReal ((Tq p)⁻¹ ^ n₀) * (ENNReal.ofReal (b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) * jN2 p f)) := by
          gcongr
          exact hj.trans (by gcongr)
      _ = ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) * jN2 p f := by
          rw [ENNReal.ofReal_mul (mul_nonneg hK0 hTn0), ENNReal.ofReal_mul hK0]
          ring
  have hEp := hFb Fp (Set.mem_insert _ _) hPp
  have hEm := hFb Fm (Set.mem_insert_of_mem _ (Set.mem_singleton Fm)) hPm
  have hTG : (Tq p / Gp p γ) ^ n₀ * (Tq p)⁻¹ ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) = (Gp p γ)⁻¹ ^ (2 * p₀ + n₀) := by
    have e : Tq p / Gp p γ * (Tq p)⁻¹ = (Gp p γ)⁻¹ := by
      rw [div_mul_eq_mul_div, mul_inv_cancel₀ hT0.ne', one_div]
    rw [← mul_pow, e, ← pow_add, add_comm]
  calc ENNReal.ofReal (Ew p (fun _ => 1) f (P.r + 1) [] γ)
      ≤ ENNReal.ofReal ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) * (Ew p (fun _ => 1) Fp (P.r + 1) [] γ + Ew p (fun _ => 1) Fm (P.r + 1) [] γ)) := ENNReal.ofReal_le_ofReal (hN.1 γ hγ hG)
    _ ≤ ENNReal.ofReal ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀)) * (ENNReal.ofReal (Ew p (fun _ => 1) Fp (P.r + 1) [] γ) + ENNReal.ofReal (Ew p (fun _ => 1) Fm (P.r + 1) [] γ)) := by
        rw [ENNReal.ofReal_mul hX0]
        gcongr
        exact ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀)) * (ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) * jN2 p f + ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) * jN2 p f) := by
        gcongr
    _ = ENNReal.ofReal ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) + (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)))) * jN2 p f := by
        rw [ENNReal.ofReal_add (mul_nonneg hX0 hZ0) (mul_nonneg hX0 hZ0), ENNReal.ofReal_mul hX0]
        ring
    _ ≤ ENNReal.ofReal (b ^ ((40 + CΛ + max 0 (Real.log C₂ / Real.log 3) + |Cκ| + 2 * C₃ * (3 * C₀ + 10)) * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) * jN2 p f := by
        gcongr ?_ * _
        apply ENNReal.ofReal_le_ofReal
        have key : (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) + (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) =
            (2 * (3 * b) ^ (2 * n₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀) := by
          rw [← hTG]; ring
        rw [key]
        exact mul_le_mul_of_nonneg_right
          (Formalism.FourierDecayAlt.P.TBBx2.Bp.const_le C₃ CΛ C₀ C₂ Cκ b Λ κ₀ P.r n₀ p₀ hC₃ hCΛ hC₀ hC₂ hb hΛ hΛb hκ hκb
            hn₀ hp₀) (by positivity)
end Formalism.FourierDecayAlt.P
