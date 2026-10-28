-- Prove2me | solution 1 for FeaturePricing.Ellipsoid.ellipsoid_pricing_regret
-- status  : ACCEPTED   (disprove)
-- author  : @sometik179
-- created : 2026-10-25T02:15:07.83662+00:00
-- url     : https://prove2.me/submissions/77f2ccfe-090d-4aa3-b388-a8251aa73d3d

import Mathlib
import Definitions.Def_FeaturePricing_Ellipsoid_EllipsoidPricing


namespace PricingProof
open Matrix FeaturePricing.Ellipsoid LinearOptimization

def features (m t : ℕ) : Fin 2 → ℝ :=
  if t < 2 * m then ![1, 0]
  else if t = 2 * m then ![0, 1]
  else if t = 2 * m + 1 then ![0, -1]
  else 0

theorem features_norm (m t : ℕ) : features m t ⬝ᵥ features m t ≤ 1 := by
  unfold features
  split_ifs <;> norm_num [dotProduct, Fin.sum_univ_two]

def diagonal (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, 0; 0, b]

end PricingProof

namespace PricingProof

theorem horizon (m : ℕ) (hm : 2 ≤ m) : 2 * m + 2 ≤ 4 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

theorem horizon_four (m : ℕ) (hm : 2 ≤ m) : 4 ≤ 4 ^ m := by
  have := horizon m hm
  omega

theorem epsilon_le (m : ℕ) (hm : 2 ≤ m) : 4 / (4 : ℝ)^m ≤ 1/4 := by
  have hp : (16 : ℝ) ≤ 4^m := by
    calc 16 = (4:ℝ)^2 := by norm_num
         _ ≤ 4^m := by exact pow_le_pow_right₀ (by norm_num) hm
  apply (div_le_iff₀ (by positivity : (0:ℝ)<4^m)).2
  nlinarith

theorem exploration_width (m t : ℕ) (hm : 2 ≤ m) (ht : t < 2*m) :
    4/(4:ℝ)^m < 2*(2/3:ℝ)^t := by
  have hmin : (2/3:ℝ)^(2*m) ≤ (2/3:ℝ)^t :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_of_lt ht)
  have hid : (4:ℝ)^m * (2/3:ℝ)^(2*m) = (16/9:ℝ)^m := by
    rw [pow_mul, ← mul_pow]
    norm_num
  have hbig : (2:ℝ) < (16/9:ℝ)^m := by
    have h := pow_le_pow_right₀ (show (1:ℝ) ≤ 16/9 by norm_num) hm
    norm_num at h
    linarith
  apply (div_lt_iff₀ (by positivity : (0:ℝ)<4^m)).2
  have hmult := mul_le_mul_of_nonneg_left hmin (le_of_lt (by positivity : (0:ℝ)<4^m))
  rw [hid] at hmult
  nlinarith

theorem quadratic_growth (m : ℕ) :
    1 + (m:ℝ)/3 + (m:ℝ)*((m:ℝ)-1)/18 ≤ (4/3:ℝ)^m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ]
    push_cast
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hmprod : 0 ≤ (m:ℝ)*((m:ℝ)-1) := by
      rcases m with _ | m
      · norm_num
      · push_cast; nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
    nlinarith

theorem choose_growth (C : ℝ) (hC : 0 < C) :
    ∃ m : ℕ, 2 ≤ m ∧ 4*C*Real.log ((4:ℝ)^m/2) < (4/3:ℝ)^m/3 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 2 (432*C*Real.log 2 + 1))
  have hm2 : 2 ≤ m := by have := (lt_of_le_of_lt (le_max_left _ _) hm); exact_mod_cast (le_of_lt this)
  have hb : 432*C*Real.log 2 + 1 < (m:ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp := quadratic_growth m
  have hmp : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmul := mul_lt_mul_of_pos_left hb hmp
  refine ⟨m, hm2, ?_⟩
  rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]
  have hl4 : Real.log 4 = 2*Real.log 2 := by
    convert (Real.log_pow (2:ℝ) 2) using 1 <;> norm_num
  rw [hl4]
  nlinarith

end PricingProof

namespace PricingProof
open Matrix FeaturePricing.Ellipsoid LinearOptimization

theorem update_e1 (a b : ℝ) (ha : a ≠ 0) :
    ellipsoidUpdateMatrix (diagonal a b) ![1, 0] = diagonal (4 * a / 9) (4 * b / 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ellipsoidUpdateMatrix, diagonal, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.vecMulVec, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply] <;> field_simp <;> ring

theorem update_e2 (a b : ℝ) (hb : b ≠ 0) :
    ellipsoidUpdateMatrix (diagonal a b) ![0, 1] = diagonal (4 * a / 3) (4 * b / 9) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ellipsoidUpdateMatrix, diagonal, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.vecMulVec, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply] <;> field_simp <;> ring

theorem width_e1 (c : Fin 2 → ℝ) (a b : ℝ) :
    bHigh c (diagonal a b) ![1, 0] - bLow c (diagonal a b) ![1, 0] = 2 * Real.sqrt a := by
  simp [bHigh, bLow, diagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem center_e1_second (c : Fin 2 → ℝ) (a b : ℝ) :
    ellipsoidUpdateCenter c (diagonal a b) ![1, 0] 1 = c 1 := by
  simp [ellipsoidUpdateCenter, diagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem center_neg_e1_second (c : Fin 2 → ℝ) (a b : ℝ) :
    ellipsoidUpdateCenter c (diagonal a b) (- ![1, 0]) 1 = c 1 := by
  simp [ellipsoidUpdateCenter, diagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem sqrt_first (t : ℕ) : Real.sqrt ((4 / 9 : ℝ) ^ t) = (2 / 3 : ℝ) ^ t := by
  have h : (4 / 9 : ℝ) ^ t = ((2 / 3 : ℝ) ^ t) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm t 2, pow_mul]
    norm_num
  rw [h, Real.sqrt_sq (pow_nonneg (by norm_num) _)]

theorem width_e2 (c : Fin 2 → ℝ) (a b : ℝ) :
    bHigh c (diagonal a b) ![0, 1] - bLow c (diagonal a b) ![0, 1] = 2 * Real.sqrt b := by
  simp [bHigh, bLow, diagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem width_neg_e2 (c : Fin 2 → ℝ) (a b : ℝ) :
    bHigh c (diagonal a b) ![0, -1] - bLow c (diagonal a b) ![0, -1] = 2 * Real.sqrt b := by
  simp [bHigh, bLow, diagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem price_explore (ε : ℝ) (c : Fin 2 → ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (hw : ε < bHigh c A x - bLow c A x) :
    priceOf ε c A x = x ⬝ᵥ c := by
  rw [priceOf, if_neg (not_le.mpr hw)]
  unfold bHigh bLow
  ring

theorem center_e2_second (c : Fin 2 → ℝ) (a r : ℝ) (hr : 0 < r) :
    ellipsoidUpdateCenter c (diagonal a (r ^ 2)) ![0, 1] 1 = c 1 + r / 3 := by
  simp [ellipsoidUpdateCenter, diagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Real.sqrt_sq hr.le]
  field_simp
  ring

end PricingProof

namespace PricingProof
open Matrix FeaturePricing.Ellipsoid LinearOptimization

theorem first_phase (m : ℕ) (hm : 2 ≤ m) (t : ℕ) (ht : t ≤ 2 * m) :
    (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) t).2 =
      diagonal ((4 / 9 : ℝ) ^ t) ((4 / 3 : ℝ) ^ t) ∧
    (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) t).1 1 = 0 := by
  induction t with
  | zero =>
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> norm_num [state, diagonal]
    · simp [state]
  | succ t ih =>
    have ht' : t < 2 * m := by omega
    obtain ⟨hshape, hcenter⟩ := ih (by omega)
    have hfeature : features m t = ![1, 0] := by simp [features, ht']
    have hw : 4 / (4 : ℝ) ^ m <
        bHigh (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) t).1
          (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) t).2 (features m t) -
        bLow (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) t).1
          (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) t).2 (features m t) := by
      rw [hshape, hfeature, width_e1, sqrt_first]
      exact exploration_width m t hm ht'
    rw [state, step, if_neg (not_le.mpr hw)]
    split_ifs
    · constructor
      · simp only [hshape, hfeature, update_e1 ((4/9:ℝ)^t) ((4/3:ℝ)^t) (ne_of_gt (pow_pos (by norm_num : (0:ℝ)<4/9) t))]
        congr 1 <;> rw [pow_succ] <;> ring
      · simpa only [hshape, hfeature, center_e1_second] using hcenter
    · constructor
      · simp only [hshape, hfeature, update_e1 ((4/9:ℝ)^t) ((4/3:ℝ)^t) (ne_of_gt (pow_pos (by norm_num : (0:ℝ)<4/9) t))]
        congr 1 <;> rw [pow_succ] <;> ring
      · simpa only [hshape, hfeature, center_neg_e1_second] using hcenter

end PricingProof

namespace PricingProof
open Matrix FeaturePricing.Ellipsoid LinearOptimization

theorem second_phase (m : ℕ) (hm : 2 ≤ m) :
    (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m+1)).2 =
      diagonal (4 * (4 / 9 : ℝ) ^ (2*m) / 3) (4 * ((4 / 3 : ℝ) ^ m) ^ 2 / 9) ∧
    (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m+1)).1 1 = (4 / 3 : ℝ) ^ m / 3 := by
  obtain ⟨hs, hc⟩ := first_phase m hm (2*m) le_rfl
  have hsq : (4 / 3 : ℝ) ^ (2*m) = ((4 / 3 : ℝ) ^ m) ^ 2 := by
    rw [Nat.mul_comm 2 m, pow_mul]
  rw [hsq] at hs
  have hr : 0 < (4 / 3 : ℝ) ^ m := pow_pos (by norm_num) _
  have hr1 : (1 : ℝ) ≤ (4 / 3 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have he := epsilon_le m hm
  have hf : features m (2*m) = ![0,1] := by simp [features]
  have hw : 4 / (4 : ℝ) ^ m <
      bHigh (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m)).1
        (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m)).2 (features m (2*m)) -
      bLow (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m)).1
        (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m)).2 (features m (2*m)) := by
    rw [hs, hf, width_e2, Real.sqrt_sq hr.le]
    linarith
  have hp : priceOf (4 / (4 : ℝ) ^ m)
      (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m)).1
      (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m)).2 (features m (2*m)) = 0 := by
    rw [price_explore _ _ _ _ hw, hf]
    simp [dotProduct, Fin.sum_univ_two, hc]
  rw [state, step, if_neg (not_le.mpr hw), if_pos (by simp [hp])]
  constructor
  · simpa only [hs, hf] using update_e2 ((4/9:ℝ)^(2*m)) (((4/3:ℝ)^m)^2) (ne_of_gt (sq_pos_of_pos hr))
  · simp only [hs, hf, center_e2_second _ _ _ hr, hc, zero_add]

end PricingProof

namespace PricingProof
open Matrix FeaturePricing.Ellipsoid LinearOptimization

theorem critical_price (m : ℕ) (hm : 2 ≤ m) :
    price 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m+1) = -(4 / 3 : ℝ) ^ m / 3 := by
  obtain ⟨hs, hc⟩ := second_phase m hm
  have hr : 0 < (4 / 3 : ℝ) ^ m := pow_pos (by norm_num) _
  have hr1 : (1 : ℝ) ≤ (4 / 3 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have he := epsilon_le m hm
  have hf : features m (2*m+1) = ![0,-1] := by simp [features]
  have hsq : 4 * ((4 / 3 : ℝ) ^ m) ^ 2 / 9 = (2 * (4 / 3 : ℝ) ^ m / 3) ^ 2 := by ring
  have hw : 4 / (4 : ℝ) ^ m <
      bHigh (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m+1)).1
        (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m+1)).2 (features m (2*m+1)) -
      bLow (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m+1)).1
        (state 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m+1)).2 (features m (2*m+1)) := by
    rw [hs, hf, width_neg_e2, hsq, Real.sqrt_sq (by positivity)]
    linarith
  unfold price center shape
  rw [price_explore _ _ _ _ hw, hf]
  simp [dotProduct, Fin.sum_univ_two, hc, neg_div]

theorem lower_bound (m : ℕ) (hm : 2 ≤ m) :
    (4 / 3 : ℝ) ^ m / 3 ≤ regret 1 (4 / (4 : ℝ) ^ m) 0 (features m) (4^m) := by
  have hp := critical_price m hm
  have hr : 0 < (4 / 3 : ℝ) ^ m := pow_pos (by norm_num) _
  have hn : 2*m+1 ∈ Finset.range (4^m) := by
    apply Finset.mem_range.mpr
    have h := horizon m hm
    omega
  have hterm : ∀ t : ℕ, 0 ≤
      (0 : Fin 2 → ℝ) ⬝ᵥ features m t -
        price 1 (4 / (4 : ℝ) ^ m) 0 (features m) t *
          (if (0 : Fin 2 → ℝ) ⬝ᵥ features m t ≥ price 1 (4 / (4 : ℝ) ^ m) 0 (features m) t then 1 else 0) := by
    intro t
    simp only [zero_dotProduct]
    split_ifs with h <;> simp_all
  unfold regret
  calc
    (4 / 3 : ℝ) ^ m / 3 =
      (0 : Fin 2 → ℝ) ⬝ᵥ features m (2*m+1) -
        price 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m+1) *
          (if (0 : Fin 2 → ℝ) ⬝ᵥ features m (2*m+1) ≥ price 1 (4 / (4 : ℝ) ^ m) 0 (features m) (2*m+1) then 1 else 0) := by
            rw [hp]
            simp [neg_div, show (0:ℝ) ≤ (4 / 3 : ℝ) ^ m / 3 by positivity]
    _ ≤ _ := Finset.single_le_sum (fun t _ => hterm t) hn

end PricingProof

open Matrix FeaturePricing.Ellipsoid

namespace PricingProof

theorem full_disproof : ¬ (∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 2 ≤ d → ∀ (R : ℝ), 0 < R → ∀ (T : ℕ), 2 * d ≤ T →
      ∀ (θ : Fin d → ℝ), θ ⬝ᵥ θ ≤ R ^ 2 →
      ∀ (x : ℕ → Fin d → ℝ), (∀ t, x t ⬝ᵥ x t ≤ 1) →
        regret R (R * (d : ℝ) ^ 2 / (T : ℝ)) θ x T ≤
          C * R * (d : ℝ) ^ 2 * Real.log ((T : ℝ) / (d : ℝ))) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨m, hm, hgrowth⟩ := choose_growth C hC
  have h := hbound 2 (by norm_num) 1 (by norm_num) (4^m)
    (by simpa using horizon_four m hm) 0 (by norm_num [dotProduct])
    (features m) (features_norm m)
  have hlower := lower_bound m hm
  norm_num only [Nat.cast_ofNat, Nat.cast_pow, one_mul] at h
  norm_num at h
  linarith

end PricingProof

open Matrix FeaturePricing.Ellipsoid

theorem FeaturePricing.Ellipsoid.ellipsoid_pricing_regret_disproof : ¬ (
∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 2 ≤ d → ∀ (R : ℝ), 0 < R → ∀ (T : ℕ), 2 * d ≤ T →
      ∀ (θ : Fin d → ℝ), θ ⬝ᵥ θ ≤ R ^ 2 →
      ∀ (x : ℕ → Fin d → ℝ), (∀ t, x t ⬝ᵥ x t ≤ 1) →
        regret R (R * (d : ℝ) ^ 2 / (T : ℝ)) θ x T ≤
          C * R * (d : ℝ) ^ 2 * Real.log ((T : ℝ) / (d : ℝ))
) := PricingProof.full_disproof

theorem solution : ¬ (
∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 2 ≤ d → ∀ (R : ℝ), 0 < R → ∀ (T : ℕ), 2 * d ≤ T →
      ∀ (θ : Fin d → ℝ), θ ⬝ᵥ θ ≤ R ^ 2 →
      ∀ (x : ℕ → Fin d → ℝ), (∀ t, x t ⬝ᵥ x t ≤ 1) →
        regret R (R * (d : ℝ) ^ 2 / (T : ℝ)) θ x T ≤
          C * R * (d : ℝ) ^ 2 * Real.log ((T : ℝ) / (d : ℝ))
) := FeaturePricing.Ellipsoid.ellipsoid_pricing_regret_disproof
