-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OneLevelCoefficients.coef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:22.182132+00:00
-- url     : https://prove2.me/submissions/facbe7d9-0b8f-47c4-9285-69b7852c7e81

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OneLevelCoefficients
open Formalism.FourierDecayAlt.TB Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.OneLevelCoefficients
theorem _root_.solution (D : Data E W) (Θ C₄ C₀ a e : ℝ) (hΘ : 1 ≤ Θ) (h4 : 1 ≤ C₄) (h0 : 2 * C₄ ≤ C₀)
    (hf : 1 ≤ D.f) (hS : D.SizesBelow Θ) (ha0 : 0 ≤ a) (ha : a ≤ 1) (_he0 : 0 ≤ e) (he : e ≤ 1)
    (i s : ℕ) (hs : 2 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.r + 1) :
    √((1 + a) * (1 + e) * C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') ≤
      ((C₀ / Θ) ^ D.f) ^ (s - 1) := by
  have hΘ0 : 0 < Θ := by linarith
  set q : ℝ := (Θ ^ D.f)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hC0 : 0 ≤ C₀ := by linarith
  have hP : ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' ≤ (q ^ 2) ^ (s - 1) := by
    calc ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' ≤ ∏ _s' ∈ Ico 1 s, q ^ 2 := by
          apply Finset.prod_le_prod (fun s' _ => hS.1 _ _)
          intro s' hs'
          rw [Finset.mem_Ico] at hs'
          exact hS.2 _ _ (by omega) hs'.1 (by omega)
      _ = (q ^ 2) ^ (s - 1) := by simp
  have hP0 : 0 ≤ ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' := Finset.prod_nonneg fun s' _ => hS.1 _ _
  have hR : ((C₀ / Θ) ^ D.f) ^ (s - 1) = (C₀ ^ D.f) ^ (s - 1) * q ^ (s - 1) := by
    rw [div_pow, div_eq_mul_inv, mul_pow]
  have hpow : 4 * C₄ ^ (D.f * s) ≤ ((C₀ ^ D.f) ^ (s - 1)) ^ 2 := by
    have e1 : ((C₀ ^ D.f) ^ (s - 1)) ^ 2 = C₀ ^ (D.f * (s - 1) * 2) := by
      rw [← pow_mul, ← pow_mul, mul_assoc]
    have e2 : (2 * C₄) ^ (D.f * (s - 1) * 2) ≤ C₀ ^ (D.f * (s - 1) * 2) :=
      pow_le_pow_left₀ (by linarith) h0 _
    have hn : 1 ≤ D.f * (s - 1) := Nat.mul_pos hf (by omega)
    have e3 : (4 : ℝ) ≤ 2 ^ (D.f * (s - 1) * 2) := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (D.f * (s - 1) * 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e4 : C₄ ^ (D.f * s) ≤ C₄ ^ (D.f * (s - 1) * 2) := by
      apply pow_le_pow_right₀ h4
      have : s ≤ (s - 1) * 2 := by omega
      calc D.f * s ≤ D.f * ((s - 1) * 2) := Nat.mul_le_mul_left _ this
        _ = D.f * (s - 1) * 2 := by ring
    rw [e1]
    refine le_trans ?_ e2
    rw [mul_pow]
    exact mul_le_mul e3 e4 (by positivity) (by positivity)
  rw [hR]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h1 : (1 + a) * (1 + e) ≤ 4 := by nlinarith
  have hc : 0 ≤ C₄ ^ (D.f * s) := by positivity
  calc (1 + a) * (1 + e) * C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s'
      ≤ 4 * C₄ ^ (D.f * s) * (q ^ 2) ^ (s - 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hc) hP hP0 (by positivity)
    _ ≤ ((C₀ ^ D.f) ^ (s - 1)) ^ 2 * (q ^ 2) ^ (s - 1) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = ((C₀ ^ D.f) ^ (s - 1) * q ^ (s - 1)) ^ 2 := by
        rw [mul_pow, ← pow_mul q, ← pow_mul q, mul_comm 2 (s - 1)]
end Formalism.FourierDecayAlt.P.OneLevelCoefficients
