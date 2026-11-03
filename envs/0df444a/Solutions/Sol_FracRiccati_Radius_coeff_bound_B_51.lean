-- Prove2me | solution 1 for FracRiccati.Radius.coeff_bound_B_51
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:07:11.989624+00:00
-- url     : https://prove2.me/submissions/be208a79-ed04-45db-b5b5-abd6f7aad683

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff

namespace Aux_FRR_B51

lemma gamma_lower (z s : ℝ) (hz : 0 < z) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    z * Real.Gamma z ≤ Real.Gamma (z + s) * (z + s) ^ (1 - s) := by
  have hzs : 0 < z + s := by linarith
  have hG : 0 < Real.Gamma (z + s) := Real.Gamma_pos_of_pos hzs
  rw [← Real.Gamma_add_one hz.ne']
  rcases eq_or_lt_of_le hs1 with h | h
  · subst h; simp
  · have key := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := z + s) (t := z + s + 1)
      (a := s) (b := 1 - s) hzs (by linarith) hs0 (by linarith) (by ring)
    have e1 : s * (z + s) + (1 - s) * (z + s + 1) = z + 1 := by ring
    rw [e1, Real.Gamma_add_one hzs.ne', Real.mul_rpow hzs.le hG.le] at key
    calc Real.Gamma (z + 1) ≤ Real.Gamma (z + s) ^ s * ((z + s) ^ (1 - s) * Real.Gamma (z + s) ^ (1 - s)) := key
      _ = (Real.Gamma (z + s) ^ s * Real.Gamma (z + s) ^ (1 - s)) * (z + s) ^ (1 - s) := by ring
      _ = Real.Gamma (z + s) * (z + s) ^ (1 - s) := by
        rw [← Real.rpow_add hG, show s + (1 - s) = 1 by ring, Real.rpow_one]

lemma gamma_ratio (α K : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hK : 1 ≤ K) :
    Real.Gamma (α * K + 1) / Real.Gamma (α * K + α + 1) ≤ (α * K) ^ (-α) := by
  have hα0 : 0 < α := by linarith
  have hαK : 0 < α * K := by positivity
  set z := α * K + 1 with hzdef
  set s := α - 1 with hsdef
  have hz : 0 < z := by linarith
  have hzs : 0 < z + s := by linarith
  have hGz : 0 < Real.Gamma z := Real.Gamma_pos_of_pos hz
  have hGzs : 0 < Real.Gamma (z + s) := Real.Gamma_pos_of_pos hzs
  have hL := gamma_lower z s hz (by linarith) (by linarith)
  have e1 : α * K + α + 1 = (z + s) + 1 := by rw [hzdef, hsdef]; ring
  rw [e1, Real.Gamma_add_one hzs.ne']
  -- lower bound denominator
  have hden : (α * K) ^ α * Real.Gamma z ≤ (z + s) * Real.Gamma (z + s) := by
    have h1 : (z + s) * Real.Gamma (z + s) = (z + s) ^ s * (Real.Gamma (z + s) * (z + s) ^ (1 - s)) := by
      rw [show (z + s) * Real.Gamma (z + s) = Real.Gamma (z + s) * (z + s) ^ (s + (1 - s)) by
        rw [show s + (1 - s) = (1:ℝ) by ring, Real.rpow_one]; ring, Real.rpow_add hzs]
      ring
    rw [h1]
    have h2 : (α * K) ^ α = (α * K) ^ s * (α * K) := by
      rw [hsdef, Real.rpow_sub hαK, Real.rpow_one]; field_simp
    rw [h2]
    have h3 : (α * K) ^ s ≤ (z + s) ^ s := Real.rpow_le_rpow hαK.le (by linarith) (by linarith)
    have h4 : (α * K) * Real.Gamma z ≤ z * Real.Gamma z := by
      apply mul_le_mul_of_nonneg_right (by linarith) hGz.le
    calc (α * K) ^ s * (α * K) * Real.Gamma z = (α * K) ^ s * ((α * K) * Real.Gamma z) := by ring
      _ ≤ (z + s) ^ s * (z * Real.Gamma z) := by
        apply mul_le_mul h3 h4 (by positivity) (by positivity)
      _ ≤ (z + s) ^ s * (Real.Gamma (z + s) * (z + s) ^ (1 - s)) := by
        apply mul_le_mul_of_nonneg_left hL (by positivity)
  rw [Real.rpow_neg hαK.le, div_le_iff₀ (by positivity)]
  have hpos : 0 < (α * K) ^ α := by positivity
  calc Real.Gamma z = ((α * K) ^ α)⁻¹ * ((α * K) ^ α * Real.Gamma z) := by field_simp
    _ ≤ ((α * K) ^ α)⁻¹ * ((z + s) * Real.Gamma (z + s)) := by
      apply mul_le_mul_of_nonneg_left hden (by positivity)

open FracRiccati.Radius

lemma coeff_rec (α : ℝ) (lam mu nu : ℂ) (j : ℕ) : coeff α lam mu nu (j + 2) =
    (lam * ∑ ℓ ∈ Finset.Ico 1 (j + 1), coeff α lam mu nu ℓ * coeff α lam mu nu (j + 1 - ℓ)
      + mu * coeff α lam mu nu (j + 1)) *
      ((Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + 1) /
          Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + α + 1) : ℝ) : ℂ) := by
  rw [coeff, Finset.sum_attach (Finset.Ico 1 (j + 1))
    (fun ℓ => coeff α lam mu nu ℓ * coeff α lam mu nu (j + 1 - ℓ))]

/-- the discrete convolution kernel bound: `ℓ^{α-1}(K-ℓ)^{α-1} ≤ (K^{α-1} 2^{1-α})^2` for `α ≥ 1`. -/
lemma kernel_bound (α K x : ℝ) (hα1 : 1 ≤ α) (hx0 : 0 ≤ x) (hxK : x ≤ K) :
    x ^ (α - 1) * (K - x) ^ (α - 1) ≤ (K ^ (α - 1) * (2 : ℝ) ^ (1 - α)) ^ 2 := by
  have hK : 0 ≤ K := hx0.trans hxK
  rw [← Real.mul_rpow hx0 (by linarith)]
  have h1 : x * (K - x) ≤ (K / 2) ^ 2 := by nlinarith [sq_nonneg (K - 2 * x)]
  have h2 : (x * (K - x)) ^ (α - 1) ≤ ((K / 2) ^ 2) ^ (α - 1) :=
    Real.rpow_le_rpow (mul_nonneg hx0 (by linarith)) h1 (by linarith)
  refine h2.trans (le_of_eq ?_)
  rw [show ((K / 2) ^ 2 : ℝ) = (K / 2) * (K / 2) by ring, Real.mul_rpow (by positivity) (by positivity),
    Real.div_rpow hK (by norm_num), show (1 - α) = -(α - 1) by ring, Real.rpow_neg (by norm_num)]
  ring

theorem bound (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (lam mu nu : ℂ) (hlam : lam ≠ 0) (hnu : nu ≠ 0) :
    let ρ : ℝ := (‖mu‖ + Real.sqrt (‖mu‖ ^ 2 +
        (2 : ℝ) ^ (2 * (2 - α)) * α ^ (α - 1) * ‖lam‖ * ‖nu‖ / Real.Gamma α)) / (2 * α ^ α)
    let C : ℝ := ‖nu‖ / (Real.Gamma (α + 1) * ρ)
    ∀ k : ℕ, 1 ≤ k → ‖coeff α lam mu nu k‖ ≤ C * (k : ℝ) ^ (α - 1) * ρ ^ k := by
  intro ρ C
  have hα0 : 0 < α := by linarith
  have hG : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα0
  have hG1 : 0 < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hGa : Real.Gamma (α + 1) = α * Real.Gamma α := Real.Gamma_add_one hα0.ne'
  have hL : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  have hN : 0 < ‖nu‖ := norm_pos_iff.mpr hnu
  set m := ‖mu‖ with hm
  set L := ‖lam‖ with hLdef
  set N := ‖nu‖ with hNdef
  set E : ℝ := (2 : ℝ) ^ (2 * (2 - α)) * α ^ (α - 1) * L * N / Real.Gamma α with hE
  have hEpos : 0 < E := by positivity
  set S := Real.sqrt (m ^ 2 + E) with hS
  have hS2 : S ^ 2 = m ^ 2 + E := Real.sq_sqrt (by positivity)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hm0 : 0 ≤ m := norm_nonneg _
  set a : ℝ := α ^ α with ha
  have hapos : 0 < a := by positivity
  have hρdef : ρ = (m + S) / (2 * a) := rfl
  have hSpos : 0 < S := Real.sqrt_pos.mpr (by positivity)
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  have hCdef : C = N / (Real.Gamma (α + 1) * ρ) := rfl
  have hC : 0 < C := by rw [hCdef]; positivity
  set p : ℝ := (2 : ℝ) ^ (1 - α) with hp
  have hp0 : 0 < p := by positivity
  -- the quadratic relation
  have hquad : L * C * p ^ 2 + m = a * ρ := by
    have h1 : a * ρ ^ 2 - m * ρ = E / (4 * a) := by
      rw [hρdef]; field_simp; nlinarith [hS2]
    have hpp : p ^ 2 * 4 = (2 : ℝ) ^ (2 * (2 - α)) := by
      rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_add (by norm_num)]
      congr 1; push_cast; ring
    have haa : α ^ (α - 1) = a / α := by rw [ha, Real.rpow_sub_one hα0.ne']
    have h2 : E / (4 * a) = L * N * p ^ 2 / Real.Gamma (α + 1) := by
      rw [hE, ← hpp, haa, hGa]; field_simp
    have h3 : L * C * p ^ 2 * ρ = L * N * p ^ 2 / Real.Gamma (α + 1) := by
      rw [hCdef]; field_simp
    have h4 : (L * C * p ^ 2 + m) * ρ = a * ρ * ρ := by nlinarith [h1, h2, h3]
    exact mul_right_cancel₀ hρ.ne' h4
  clear_value p a S E C ρ
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    match k, ih, hk with
    | 0, _, hk => omega
    | 1, _, _ =>
      simp only [coeff, Nat.cast_one, Real.one_rpow, mul_one, pow_one]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hG1.le, hCdef]
      apply le_of_eq
      field_simp
      exact hNdef.symm
    | j + 2, ih, _ =>
      obtain ⟨K, hKdef⟩ : ∃ K, K = j + 1 := ⟨_, rfl⟩
      rw [coeff_rec, ← hKdef]
      have hK1 : (1 : ℝ) ≤ (K : ℝ) := by rw [hKdef]; push_cast; linarith
      have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
      set A : ℝ := (K : ℝ) ^ (α - 1) with hA
      have hA1 : 1 ≤ A := Real.one_le_rpow hK1 (by linarith)
      set g : ℝ := Real.Gamma (α * (K : ℝ) + 1) / Real.Gamma (α * (K : ℝ) + α + 1) with hg
      have hg0 : 0 ≤ g := div_nonneg (Real.Gamma_pos_of_pos (by positivity)).le
        (Real.Gamma_pos_of_pos (by positivity)).le
      have hgle : g ≤ 1 / (a * (K * A)) := by
        have := gamma_ratio α K hα1 hα2 hK1
        refine this.trans (le_of_eq ?_)
        rw [Real.rpow_neg (by positivity), Real.mul_rpow hα0.le hK0.le, hA,
          Real.rpow_sub_one hK0.ne', ha]
        field_simp
      -- bound on the convolution
      have hconv : ‖∑ ℓ ∈ Finset.Ico 1 K, coeff α lam mu nu ℓ * coeff α lam mu nu (K - ℓ)‖ ≤
          (K : ℝ) * (C ^ 2 * ρ ^ K * (A * p) ^ 2) := by
        refine (norm_sum_le _ _).trans ?_
        have hterm : ∀ ℓ ∈ Finset.Ico 1 K,
            ‖coeff α lam mu nu ℓ * coeff α lam mu nu (K - ℓ)‖ ≤ C ^ 2 * ρ ^ K * (A * p) ^ 2 := by
          intro ℓ hℓ
          rw [Finset.mem_Ico] at hℓ
          rw [norm_mul]
          have b1 := ih ℓ (by omega) (by omega)
          have b2 := ih (K - ℓ) (by omega) (by omega)
          have hcast : ((K - ℓ : ℕ) : ℝ) = (K : ℝ) - ℓ := by rw [Nat.cast_sub (by omega)]
          rw [hcast] at b2
          have hkb : (ℓ : ℝ) ^ (α - 1) * ((K : ℝ) - ℓ) ^ (α - 1) ≤ (A * p) ^ 2 := by
            rw [hA, hp]; exact kernel_bound α K ℓ hα1.le (by positivity) (by exact_mod_cast hℓ.2.le)
          have hρK : ρ ^ ℓ * ρ ^ (K - ℓ) = ρ ^ K := by rw [← pow_add]; congr 1; omega
          calc ‖coeff α lam mu nu ℓ‖ * ‖coeff α lam mu nu (K - ℓ)‖
              ≤ (C * (ℓ : ℝ) ^ (α - 1) * ρ ^ ℓ) * (C * ((K : ℝ) - ℓ) ^ (α - 1) * ρ ^ (K - ℓ)) :=
                mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
            _ = C ^ 2 * (ρ ^ ℓ * ρ ^ (K - ℓ)) * ((ℓ : ℝ) ^ (α - 1) * ((K : ℝ) - ℓ) ^ (α - 1)) := by ring
            _ ≤ C ^ 2 * ρ ^ K * (A * p) ^ 2 := by
              rw [hρK]; exact mul_le_mul_of_nonneg_left hkb (by positivity)
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : ((K - 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.sub_le K 1
        exact this
      have hprev := ih K (by omega) (by omega)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hg0]
      have hcK : ((j + 2 : ℕ) : ℝ) = (K : ℝ) + 1 := by rw [hKdef]; push_cast; ring
      rw [hcK, show j + 2 = K + 1 by omega]
      rw [← hA] at hprev
      have hX : ‖lam * ∑ ℓ ∈ Finset.Ico 1 K, coeff α lam mu nu ℓ * coeff α lam mu nu (K - ℓ) +
          mu * coeff α lam mu nu K‖ ≤
          L * ((K : ℝ) * (C ^ 2 * ρ ^ K * (A * p) ^ 2)) + m * (C * A * ρ ^ K) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hconv hL.le)
          (mul_le_mul_of_nonneg_left hprev hm0)
      have hA' : A ≤ ((K : ℝ) + 1) ^ (α - 1) := Real.rpow_le_rpow hK0.le (by linarith) (by linarith)
      have hmK : m / K ≤ m * A := by
        exact (div_le_self hm0 hK1).trans (le_mul_of_one_le_right hm0 hA1)
      clear_value A g
      calc ‖lam * ∑ ℓ ∈ Finset.Ico 1 K, coeff α lam mu nu ℓ * coeff α lam mu nu (K - ℓ) +
            mu * coeff α lam mu nu K‖ * g
          ≤ (L * ((K : ℝ) * (C ^ 2 * ρ ^ K * (A * p) ^ 2)) + m * (C * A * ρ ^ K)) *
              (1 / (a * (K * A))) := mul_le_mul hX hgle hg0 (by positivity)
        _ = C * ρ ^ K * (L * C * A * p ^ 2 + m / K) / a := by
              field_simp
        _ ≤ C * ρ ^ K * (A * (L * C * p ^ 2 + m)) / a := by
              have h5 : L * C * A * p ^ 2 + m / K ≤ A * (L * C * p ^ 2 + m) := by
                have e1 : L * C * A * p ^ 2 = A * (L * C * p ^ 2) := by ring
                have e2 : A * (L * C * p ^ 2 + m) = A * (L * C * p ^ 2) + m * A := by ring
                rw [e1, e2]; exact add_le_add_right hmK _
              exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h5 (by positivity)) hapos.le
        _ = C * A * ρ ^ (K + 1) := by
              rw [hquad, pow_succ]; field_simp
        _ ≤ C * ((K : ℝ) + 1) ^ (α - 1) * ρ ^ (K + 1) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_left hA' hC.le

end Aux_FRR_B51

open FracRiccati.Radius in
theorem solution (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (lam mu nu : ℂ) (hlam : lam ≠ 0) (hnu : nu ≠ 0) :
    let ρ : ℝ := (‖mu‖ + Real.sqrt (‖mu‖ ^ 2 +
        (2 : ℝ) ^ (2 * (2 - α)) * α ^ (α - 1) * ‖lam‖ * ‖nu‖ / Real.Gamma α)) / (2 * α ^ α)
    let C : ℝ := ‖nu‖ / (Real.Gamma (α + 1) * ρ)
    ∀ k : ℕ, 1 ≤ k → ‖coeff α lam mu nu k‖ ≤ C * (k : ℝ) ^ (α - 1) * ρ ^ k :=
  Aux_FRR_B51.bound α hα1 hα2 lam mu nu hlam hnu
