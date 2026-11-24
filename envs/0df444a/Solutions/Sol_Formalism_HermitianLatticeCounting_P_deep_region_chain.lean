-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.deep_region_chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:21.690334+00:00
-- url     : https://prove2.me/submissions/482f9a32-6602-46bb-a219-080bbfcbd543

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_le_rpow_two_mul
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ydat_facts
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_b1_bound_le_power

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DeepChain := by
  intro C hC
  refine ⟨C ^ 2 + 12 * C + 31, by nlinarith, ?_⟩
  intro n q f rd g b τ₁ τs ρ Kxx Bs D volG volK hn hq hqn hf hrd hg hb hτ hττ hD hvK hvG hρ0 hρ hK hB hvol
  obtain ⟨hY, hnY, hfY, hrdY, hgY, hbY⟩ := ydat_facts hn hf hrd hg hb
  have hqn' : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hqn
  have hb1 := b1_bound_le_power (f := f) hqn' hY hnY hfY (by linarith) hbY
  have hb10 : 0 ≤ b1 n q f b := by unfold b1; positivity
  generalize Ydat n f rd g b = Y at *
  generalize b1 n q f b = b₁ at *
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hq0 : q ≠ 0 := by omega
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg _
  set m : ℕ := n ^ 2 * f with hm
  have hmr : (m:ℝ) = (n:ℝ) ^ 2 * f := by rw [hm]; push_cast; ring
  have hP : 2 * P0 n q f = q * (16 * m) := by rw [hm]; unfold P0; ring
  have e4 : 4 * n ^ 2 * f = 4 * m := by rw [hm]; ring
  have e12 : 12 * n ^ 2 * f = 12 * m := by rw [hm]; ring
  have e16 : 16 * q * n ^ 2 * f = q * (16 * m) := by rw [hm]; ring
  rw [hP] at hK
  rw [e4] at hB
  rw [e12, e16]
  set W := (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b₁ with hW
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hx0 : 0 ≤ (2 * τ₁) ^ ((1:ℝ) / q) := by positivity
  have hT : (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) ≤ (C ^ 2 * W) ^ (q * (16 * m)) * (2 * τ₁) ^ (16 * m) := by
    calc (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m))
        ≤ (C * (C * (n:ℝ) ^ 2 * f * g * rd * (2 * τ₁) ^ ((1:ℝ) / q)) * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) := by
          gcongr
      _ = ((C ^ 2 * W) * (2 * τ₁) ^ ((1:ℝ) / q)) ^ (q * (16 * m)) := by
          congr 1; rw [hW]; ring
      _ = (C ^ 2 * W) ^ (q * (16 * m)) * ((2 * τ₁) ^ ((1:ℝ) / q)) ^ (q * (16 * m)) := mul_pow _ _ _
      _ = _ := by
        congr 1
        rw [pow_mul, one_div, Real.rpow_inv_natCast_pow (by linarith) hq0]
  have hT0 : 0 ≤ (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) := by positivity
  have s1 : volG * Kxx ≤ (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) * D
      * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C / τ₁) ^ (4 * m) * (C * n * rd * g) ^ m := by
    calc volG * Kxx ≤ volG * ((C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m))
          * (D * volK⁻¹ * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C / τ₁) ^ (4 * m))) := by
          apply mul_le_mul_of_nonneg_left _ hvG
          exact hK.trans (mul_le_mul_of_nonneg_left hB hT0)
      _ = (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) * D
          * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C / τ₁) ^ (4 * m) * (volG / volK) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ _ := by gcongr
  have s2 : (2 * τ₁) ^ (16 * m) * (C / τ₁) ^ (4 * m) = (2 ^ 16 * C ^ 4) ^ m * τ₁ ^ (12 * m) := by
    have : 16 * m = 12 * m + 4 * m := by ring
    rw [mul_pow 2 τ₁, div_pow]
    conv_lhs => rw [this, pow_add τ₁]
    have h4 : τ₁ ^ (4 * m) ≠ 0 := by positivity
    rw [← this, mul_pow, ← pow_mul, ← pow_mul]
    field_simp
  have hCY := le_rpow_two_mul hY (by linarith : 0 ≤ C)
  have s3 : 2 ^ 16 * C ^ 4 * (C * (n:ℝ) ^ 2 * b₁) * (C * n * rd * g) ≤ Y ^ (12 * C + 31) := by
    have e : Y ^ (12 * C + 31) = Y ^ 16 * (Y ^ (2 * C)) ^ 4 * (Y ^ (2 * C) * Y ^ 2 * Y ^ 10)
        * (Y ^ (2 * C) * Y * Y * Y) := by
      rw [Real.rpow_add hY0]
      have h31 : Y ^ (31:ℝ) = Y ^ 31 := by exact_mod_cast Real.rpow_natCast Y 31
      have h12 : Y ^ (12 * C) = (Y ^ (2 * C)) ^ 6 := by
        rw [← Real.rpow_mul_natCast hY0.le]; congr 1; push_cast; ring
      rw [h31, h12]; ring
    rw [e]
    gcongr
  have s4 : (2 ^ 16 * C ^ 4) ^ m * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C * n * rd * g) ^ m
      ≤ Y ^ ((C ^ 2 + 12 * C + 31) * (n:ℝ) ^ 2 * f) := by
    rw [← mul_pow, ← mul_pow]
    calc _ ≤ (Y ^ (12 * C + 31)) ^ m := by
          apply pow_le_pow_left₀ (by positivity) s3
      _ = Y ^ ((12 * C + 31) * m) := (Real.rpow_mul_natCast hY0.le _ _).symm
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hY1
        rw [hmr]
        have hm0 : 0 ≤ (n:ℝ) ^ 2 * f := by positivity
        nlinarith [sq_nonneg C]
  have s5 : (C ^ 2 * W) ^ (q * (16 * m)) ≤ ((C ^ 2 + 12 * C + 31) * (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b₁) ^ (q * (16 * m)) := by
    apply pow_le_pow_left₀ (by positivity)
    have : (C ^ 2 + 12 * C + 31) * (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b₁ = (C ^ 2 + 12 * C + 31) * W := by
      rw [hW]; ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ hW0
    linarith
  have s6 : τ₁ ^ (12 * m) ≤ τs ^ (12 * m) := by gcongr
  calc volG * Kxx ≤ (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) * D
      * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C / τ₁) ^ (4 * m) * (C * n * rd * g) ^ m := s1
    _ ≤ ((C ^ 2 * W) ^ (q * (16 * m)) * (2 * τ₁) ^ (16 * m)) * D
      * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C / τ₁) ^ (4 * m) * (C * n * rd * g) ^ m := by gcongr
    _ = D * ((2 * τ₁) ^ (16 * m) * (C / τ₁) ^ (4 * m) * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C * n * rd * g) ^ m)
        * (C ^ 2 * W) ^ (q * (16 * m)) := by ring
    _ = D * ((2 ^ 16 * C ^ 4) ^ m * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C * n * rd * g) ^ m)
        * (C ^ 2 * W) ^ (q * (16 * m)) * τ₁ ^ (12 * m) := by rw [s2]; ring
    _ ≤ _ := by gcongr
end Formalism.HermitianLatticeCounting.P
