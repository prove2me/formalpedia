-- Prove2me | solution 1 for EisensteinGeneral.LocalCorrection.exists_forall_norm_corrOn_le_of_le_re
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fefd8dae-18be-5d8b-8a29-3f15155f318d

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Definitions.Def_EisensteinGeneral_LocalCorrection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EisensteinGeneral_LocalCorrection_exists_forall_norm_corrOn_le_of_le_re

set_option autoImplicit false

open EisensteinGeneral.LocalCorrection

namespace S3bAux

theorem norm_cpow_neg_two_mul_add_one_le {N : ℕ} (hN : 1 ≤ N) {σ₁ : ℝ} {s : ℂ} (hs : σ₁ ≤ s.re) :
    ‖((N : ℕ) : ℂ) ^ (-(2 * s + 1))‖ ≤ (N : ℝ) ^ (2 * max 0 (-σ₁) + 1) := by
  rw [Complex.norm_natCast_cpow_of_pos hN]
  refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) ?_
  have h' := le_max_right 0 (-σ₁)
  have h'' := le_max_left 0 (-σ₁)
  simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero, Complex.one_re]
  linarith

theorem ramSum_norm_le {N : ℕ} (hN : 1 ≤ N) (K : ℕ) {c₀ : ℂ} {c₀' : ℝ} (hc₀ : ‖c₀‖ ≤ c₀')
    {sh : ℕ → ℂ} {b d : ℝ} (hb : 0 ≤ b) (hd : 1 ≤ d) (hsh : ∀ k, 1 ≤ k → ‖sh k‖ ≤ b * d ^ k) {σ₁ : ℝ} {s : ℂ}
    (hs : σ₁ ≤ s.re) :
    ‖ramSum N K c₀ sh s‖ ≤ c₀' + (K : ℝ) * (b * ((N : ℝ) ^ (2 * max 0 (-σ₁) + 1) * d) ^ K) := by
  have hR : (0 : ℝ) ≤ max 0 (-σ₁) := le_max_left _ _
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb1 : (1 : ℝ) ≤ (N : ℝ) ^ (2 * max 0 (-σ₁) + 1) * d :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN' (by positivity)) hd
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      ‖(((N : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k * sh k‖ ≤ b * ((N : ℝ) ^ (2 * max 0 (-σ₁) + 1) * d) ^ K := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
    rw [norm_mul, norm_pow]
    calc ‖((N : ℕ) : ℂ) ^ (-(2 * s + 1))‖ ^ k * ‖sh k‖
        ≤ ((N : ℝ) ^ (2 * max 0 (-σ₁) + 1)) ^ k * (b * d ^ k) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_cpow_neg_two_mul_add_one_le hN hs) k)
            (hsh k hk1) (norm_nonneg _) (by positivity)
      _ = b * ((N : ℝ) ^ (2 * max 0 (-σ₁) + 1) * d) ^ k := by rw [mul_pow]; ring
      _ ≤ b * ((N : ℝ) ^ (2 * max 0 (-σ₁) + 1) * d) ^ K :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 hkK) hb
  unfold ramSum
  refine (norm_add_le _ _).trans (add_le_add hc₀ ?_)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

theorem succ_le_two_pow (M : ℕ) : M + 1 ≤ 2 ^ M := by
  induction M with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

end S3bAux

open S3bAux in
theorem solution
    {N : ℕ} (hN : 2 ≤ N) (n : ℤ) (c₀ m₀ : ℕ) {μ𝒪 : ℝ} (hμ : 0 < μ𝒪)
    (c₀' b d σ₁ : ℝ) (hc₀' : 0 ≤ c₀') (hb : 0 ≤ b) (hd : 1 ≤ d) :
    ∃ E : ℝ, ∃ κ : ℕ, 0 ≤ E ∧ ∀ (c m : ℕ) (e : ℤ) (γ₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ),
      c ≤ c₀ → m ≤ m₀ → ‖γ₀‖ ≤ c₀' → (∀ k, 1 ≤ k → ‖sh k‖ ≤ b * d ^ k) → σ₁ ≤ s.re →
        ‖corrOn N n c m e μ𝒪 γ₀ sh s‖ ≤ E * ((N : ℝ) ^ (-e).toNat) ^ κ := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set R' : ℝ := max 0 (-σ₁) with hR'
  have hR : 0 ≤ R' := le_max_left _ _
  set D : ℝ := (N : ℝ) ^ (2 * R' + 1) * d with hD
  have hD1 : 1 ≤ D := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN1' (by positivity)) hd
  obtain ⟨κ, hκ⟩ := pow_unbounded_of_one_lt (2 * D) (by norm_num : (1 : ℝ) < 2)
  have h2D : 2 * D ≤ (N : ℝ) ^ κ := hκ.le.trans (pow_le_pow_left₀ (by norm_num) hN2 κ)
  set K₀ : ℕ := m₀ + n.toNat + c₀ with hK₀
  refine ⟨μ𝒪⁻¹ * ((c₀' + b) * (2 * D) ^ K₀), κ, by positivity, fun c m e γ₀ sh s hc hm hγ₀ hsh hs => ?_⟩
  unfold corrOn
  split_ifs with he
  · set K := (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat with hK
    have hKle : K ≤ K₀ + (-e).toNat := by
      rw [hK, hK₀]; omega
    have hram : ‖ramSum N K γ₀ sh s‖ ≤ c₀' + (K : ℝ) * (b * D ^ K) := ramSum_norm_le hN1 K hγ₀ hb hd hsh hs
    have hK2 : (K : ℝ) ≤ 2 ^ K := by exact_mod_cast (Nat.le_succ K).trans (succ_le_two_pow K)
    have h1 : (K : ℝ) * (b * D ^ K) ≤ b * (2 * D) ^ K := by
      calc (K : ℝ) * (b * D ^ K) = b * (K * D ^ K) := by ring
        _ ≤ b * (2 ^ K * D ^ K) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK2 (by positivity)) hb
        _ = b * (2 * D) ^ K := by ring
    have h1le : (1 : ℝ) ≤ (2 * D) ^ K := one_le_pow₀ (by linarith)
    have h2 : c₀' + b * (2 * D) ^ K ≤ (c₀' + b) * (2 * D) ^ K := by
      have h := mul_le_mul_of_nonneg_left h1le hc₀'
      rw [mul_one] at h
      linarith
    have h3 : (2 * D) ^ K ≤ (2 * D) ^ K₀ * ((N : ℝ) ^ (-e).toNat) ^ κ := by
      calc (2 * D) ^ K ≤ (2 * D) ^ (K₀ + (-e).toNat) := pow_le_pow_right₀ (by linarith) hKle
        _ = (2 * D) ^ K₀ * (2 * D) ^ (-e).toNat := pow_add _ _ _
        _ ≤ (2 * D) ^ K₀ * ((N : ℝ) ^ κ) ^ (-e).toNat :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2D _) (by positivity)
        _ = (2 * D) ^ K₀ * ((N : ℝ) ^ (-e).toNat) ^ κ := by ring
    calc ‖(μ𝒪 : ℂ)⁻¹ * ramSum N K γ₀ sh s‖ = μ𝒪⁻¹ * ‖ramSum N K γ₀ sh s‖ := by
          rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hμ.le]
      _ ≤ μ𝒪⁻¹ * ((c₀' + b) * (2 * D) ^ K₀ * ((N : ℝ) ^ (-e).toNat) ^ κ) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hμ.le)
          calc ‖ramSum N K γ₀ sh s‖ ≤ c₀' + (K : ℝ) * (b * D ^ K) := hram
            _ ≤ c₀' + b * (2 * D) ^ K := by linarith
            _ ≤ (c₀' + b) * (2 * D) ^ K := h2
            _ ≤ (c₀' + b) * ((2 * D) ^ K₀ * ((N : ℝ) ^ (-e).toNat) ^ κ) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = _ := by ring
      _ = _ := by ring
  · rw [norm_zero]; positivity

end S_EisensteinGeneral_LocalCorrection_exists_forall_norm_corrOn_le_of_le_re
end P2MW
export P2MW.S_EisensteinGeneral_LocalCorrection_exists_forall_norm_corrOn_le_of_le_re (solution)
