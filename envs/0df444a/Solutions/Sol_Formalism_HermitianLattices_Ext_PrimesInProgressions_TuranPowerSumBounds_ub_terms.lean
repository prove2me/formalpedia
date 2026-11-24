-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.ub_terms
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:41.041646+00:00
-- url     : https://prove2.me/submissions/1ae9925d-b348-4662-a95a-ce1478363c87

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TwentyFiveMulSmallConstant
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_UbTerms
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_fact_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_rr_gt
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_twentyFive_mul_smallConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Complex
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
private theorem pow_mul_div_pow_succ_eq_div (η X : ℝ) (hη : η ≠ 0) (j : ℕ) :
    η ^ j * (X / η ^ (j + 1)) = X / η := by
  first
  | rw [mul_div_assoc', pow_succ η j, mul_div_mul_left _ _ (pow_ne_zero j hη)]
  | (field_simp; done)
  | (field_simp; ring)
private theorem pow_mul_div_mul_pow_eq_div (η M X : ℝ) (hη : η ≠ 0) (j : ℕ) :
    η ^ j * (X / (M * η ^ j)) = X / M := by
  first
  | rw [mul_div_assoc', mul_comm M (η ^ j), mul_div_mul_left _ _ (pow_ne_zero j hη)]
  | (field_simp; done)
  | (field_simp; ring)
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
set_option maxHeartbeats 800000
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
theorem _root_.solution (a : ℕ) (CP CF cZ cS c₂ κ L ℓ lam η Mr K : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hCP : 0 < CP) (hCF : 0 < CF) (hcZ : 0 < cZ) (hcS : 0 < cS) (hc₂ : 0 < c₂)
    (hL : 1 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 2 * L) (hlam : 0 < lam) (hη : 0 < η) (hMr : 0 < Mr) (hK : 0 < K)
    (hlη1 : lam / η ≤ 2 * (lam * L) / cZ) (hM : ℓ ^ 2 / Mr ≤ 32 * lam / cS) (hηc : η ≤ c0 a)
    (hηL : η * L < c₂ * K) (h25c : 25 * CF * c₂ ≤ κ) (hκth : κ ≤ th a)
    (hc₂P : 2 * Real.exp 1 * CP * c₂ * rr a ≤ th a) (hjr : th a * K < j) :
    η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1) + (CP * ℓ) ^ j / ((j - 1).factorial : ℝ)
        + CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j) + 2 * j * lam / η ^ (j + 1) + CF * L * 25 ^ j) ≤
      (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)
        + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
  have hR16 := rr_gt a
  have hRpos : 0 < rr a := by linarith
  have hRne : rr a ≠ 0 := hRpos.ne'
  have hηne : η ≠ 0 := hη.ne'
  have hL0 : 0 < L := by linarith
  have hJ1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hJpos : (0 : ℝ) < j := by linarith
  have hJsq : (j : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by linarith [sq_nonneg (j : ℝ)]
  have hL2 : 1 ≤ L ^ 2 := by linarith [mul_le_mul hL hL zero_le_one hL0.le]
  have hLL3 : L ≤ L ^ 3 := by linarith [mul_le_mul_of_nonneg_left hL2 hL0.le]
  have hL3 : 1 ≤ L ^ 3 := by linarith
  have hJ1sq : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) ^ 2 * L ^ 3 := by
    linarith [mul_le_mul_of_nonneg_left hL3 (sq_nonneg ((j : ℝ) + 1)), sq_nonneg (j : ℝ)]
  have hJL : (j : ℝ) * L ≤ ((j : ℝ) + 1) ^ 2 * L ^ 3 := mul_le_mul hJsq hLL3 hL0.le (by positivity)
  have hℓ2 : ℓ ^ 2 ≤ 4 * L ^ 2 := by
    linarith [mul_le_mul hℓ hℓ hℓ0 (by linarith : (0 : ℝ) ≤ 2 * L)]
  have b1 : η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1)) ≤ 8 * CP / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by
    rw [pow_mul_div_pow_succ_eq_div η _ hηne j]
    calc CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η = CP * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 * (lam / η) := by ring
      _ ≤ CP * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 * (2 * (lam * L) / cZ) :=
          mul_le_mul_of_nonneg_left hlη1 (by positivity)
      _ = 2 * CP * lam * L / cZ * ((j : ℝ) + 1) ^ 2 * ℓ ^ 2 := by ring
      _ ≤ 2 * CP * lam * L / cZ * ((j : ℝ) + 1) ^ 2 * (4 * L ^ 2) :=
          mul_le_mul_of_nonneg_left hℓ2 (by positivity)
      _ = 8 * CP / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by ring
  have b3 : η ^ j * (CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j)) ≤ 32 * CP / cS * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by
    rw [pow_mul_div_mul_pow_eq_div η Mr _ hηne j]
    calc CP * ((j : ℝ) + 1) * ℓ ^ 2 / Mr = CP * ((j : ℝ) + 1) * (ℓ ^ 2 / Mr) := by ring
      _ ≤ CP * ((j : ℝ) + 1) * (32 * lam / cS) := mul_le_mul_of_nonneg_left hM (by positivity)
      _ = 32 * CP / cS * lam * ((j : ℝ) + 1) := by ring
      _ ≤ 32 * CP / cS * lam * (((j : ℝ) + 1) ^ 2 * L ^ 3) := mul_le_mul_of_nonneg_left hJ1sq (by positivity)
      _ = 32 * CP / cS * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by ring
  have b4 : η ^ j * (2 * (j : ℝ) * lam / η ^ (j + 1)) ≤ 4 / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by
    rw [pow_mul_div_pow_succ_eq_div η _ hηne j]
    calc 2 * (j : ℝ) * lam / η = 2 * (j : ℝ) * (lam / η) := by ring
      _ ≤ 2 * (j : ℝ) * (2 * (lam * L) / cZ) := mul_le_mul_of_nonneg_left hlη1 (by positivity)
      _ = 4 / cZ * lam * ((j : ℝ) * L) := by ring
      _ ≤ 4 / cZ * lam * (((j : ℝ) + 1) ^ 2 * L ^ 3) := mul_le_mul_of_nonneg_left hJL (by positivity)
      _ = 4 / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by ring
  have hx0 : 0 ≤ CP * ℓ * η := by positivity
  have hxK : CP * ℓ * η ≤ 2 * CP * c₂ * K := by
    have e1 : CP * η * ℓ ≤ CP * η * (2 * L) := mul_le_mul_of_nonneg_left hℓ (by positivity)
    have e2 : CP * (η * L) ≤ CP * (c₂ * K) := mul_le_mul_of_nonneg_left hηL.le hCP.le
    linarith
  have hexR : Real.exp 1 * (CP * ℓ * η) * rr a ≤ th a * K := by
    calc Real.exp 1 * (CP * ℓ * η) * rr a
        ≤ Real.exp 1 * (2 * CP * c₂ * K) * rr a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxK (Real.exp_pos 1).le) hRpos.le
      _ = (2 * Real.exp 1 * CP * c₂ * rr a) * K := by ring
      _ ≤ th a * K := mul_le_mul_of_nonneg_right hc₂P hK.le
  have hy : Real.exp 1 * (CP * ℓ * η) / (j : ℝ) ≤ 1 / rr a := by
    first
    | (rw [div_le_div_iff₀ hJpos hRpos]; linarith)
    | (rw [div_le_div_iff hJpos hRpos]; linarith)
    | (rw [div_le_div_iff_of_pos hJpos hRpos]; linarith)
  have b2 : η ^ j * ((CP * ℓ) ^ j / ((j - 1).factorial : ℝ)) ≤ ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
    calc η ^ j * ((CP * ℓ) ^ j / ((j - 1).factorial : ℝ)) = (CP * ℓ * η) ^ j / ((j - 1).factorial : ℝ) := by ring
      _ ≤ (j : ℝ) * (Real.exp 1 * (CP * ℓ * η) / j) ^ j := fact_bound _ hx0 j hj
      _ ≤ (j : ℝ) * (1 / rr a) ^ j := by
          first
          | exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hy j) hJpos.le
          | exact mul_le_mul_of_nonneg_left (pow_le_pow_left (by positivity) hy j) hJpos.le
          | gcongr (j : ℝ) * ?_ ^ j
      _ = (j : ℝ) / rr a ^ j := by rw [one_div_pow, mul_one_div]
      _ ≤ ((j : ℝ) + 1) ^ 2 / rr a ^ j := by gcongr
  have b5 : η ^ j * (CF * L * 25 ^ j) ≤ rr a * (((j : ℝ) + 1) ^ 2 / rr a ^ j) := by
    have h25 : 25 * η ≤ 1 / rr a := by
      have := twentyFive_mul_smallConstant a
      linarith
    have hcl : 25 * (CF * η * L) ≤ (j : ℝ) := by
      have e1 : CF * (η * L) ≤ CF * (c₂ * K) := mul_le_mul_of_nonneg_left hηL.le hCF.le
      have e2 : 25 * CF * c₂ * K ≤ th a * K :=
        mul_le_mul_of_nonneg_right (h25c.trans hκth) hK.le
      linarith
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    calc η ^ (k + 1) * (CF * L * 25 ^ (k + 1)) = 25 * (CF * η * L) * (25 * η) ^ k := by ring
      _ ≤ ((k + 1 : ℕ) : ℝ) * (1 / rr a) ^ k := by
          first
          | exact mul_le_mul hcl (pow_le_pow_left₀ (by positivity) h25 k) (by positivity) (by positivity)
          | exact mul_le_mul hcl (pow_le_pow_left (by positivity) h25 k) (by positivity) (by positivity)
      _ = ((k + 1 : ℕ) : ℝ) / rr a ^ k := by rw [one_div_pow, mul_one_div]
      _ ≤ (((k + 1 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ k := by gcongr
      _ = rr a * ((((k + 1 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ (k + 1)) := by
          rw [pow_succ (rr a) k, mul_div_assoc', mul_comm (rr a ^ k) (rr a),
            mul_div_mul_left _ _ hRne]
  have hsplit : η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1) + (CP * ℓ) ^ j / ((j - 1).factorial : ℝ) + CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j) + 2 * (j : ℝ) * lam / η ^ (j + 1) + CF * L * 25 ^ j)
      = η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1)) + η ^ j * ((CP * ℓ) ^ j / ((j - 1).factorial : ℝ)) + η ^ j * (CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j)) + η ^ j * (2 * (j : ℝ) * lam / η ^ (j + 1)) + η ^ j * (CF * L * 25 ^ j) := by
    ring
  have hfin : 8 * CP / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) + ((j : ℝ) + 1) ^ 2 / rr a ^ j + 32 * CP / cS * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) + 4 / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) + rr a * (((j : ℝ) + 1) ^ 2 / rr a ^ j) = (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3) + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by ring
  rw [hsplit]
  exact (add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5).trans_eq hfin
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
