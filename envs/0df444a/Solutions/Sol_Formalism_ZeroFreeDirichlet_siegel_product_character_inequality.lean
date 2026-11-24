-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.siegel_product_character_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:14:34.222508+00:00
-- url     : https://prove2.me/submissions/a6137d98-b006-4cec-bc2e-b809d781c339

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelBoundSameCharacter
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelProductCharacterInequality
import Theorems.Thm_Formalism_ZeroFreeDirichlet_agree_coprime_of_product_principal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex
noncomputable section
namespace Formalism.ZeroFreeDirichlet
private theorem two_pow_card_primeFactors_le_self (n : ℕ) (hn : n ≠ 0) : 2 ^ n.primeFactors.card ≤ n := by
  calc 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
private theorem card_primeFactors_add_one_sq_le_rpow {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : n ≠ 0) :
    ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤ (2 / (ε * Real.log 2) + 1) ^ 2 * (n : ℝ) ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have h2 : (2 : ℝ) ^ n.primeFactors.card ≤ n := by exact_mod_cast two_pow_card_primeFactors_le_self n hn
  have hcard : (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow] at this
  have hlog : Real.log n ≤ (n : ℝ) ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div (by linarith) (by linarith)
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < ε / 2)] at hlog
  have hR1 : 1 ≤ (n : ℝ) ^ (ε / 2) := Real.one_le_rpow hn1 (by linarith)
  have hc : (n.primeFactors.card : ℝ) ≤ 2 / (ε * Real.log 2) * (n : ℝ) ^ (ε / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hε hl2)]
    nlinarith [mul_le_mul_of_nonneg_right hcard (by linarith : (0 : ℝ) ≤ ε / 2)]
  have hb : (n.primeFactors.card : ℝ) + 1 ≤ (2 / (ε * Real.log 2) + 1) * (n : ℝ) ^ (ε / 2) := by
    nlinarith
  have h0 : 0 ≤ (n.primeFactors.card : ℝ) + 1 := by positivity
  calc ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤ ((2 / (ε * Real.log 2) + 1) * (n : ℝ) ^ (ε / 2)) ^ 2 :=
        pow_le_pow_left₀ h0 hb 2
    _ = (2 / (ε * Real.log 2) + 1) ^ 2 * (n : ℝ) ^ ε := by
        rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (ε / 2)) 2, ← Real.rpow_mul (by positivity)]
        norm_num
private theorem div_le_mul_of_main_bound_caseA {σ ε C L₁ X Lψ Nk M Q Pc A : ℝ} (hε : 0 < ε) (h1σ : 0 < 1 - σ)
    (hL₁ : 0 < L₁) (hX : 0 ≤ X) (hA : 0 < A) (hNk0 : 0 ≤ Nk) (hLψ0 : 0 ≤ Lψ) (hM0 : 0 ≤ M)
    (hmain : (1 - σ) / 2 ≤ C * (L₁ * X * Lψ) * Nk) (hLψ : Lψ ≤ A * (M / (ε / 2))) (hNk : Nk ≤ M)
    (hMM : M * M = Pc * Q) (hPc : 0 < Pc) :
    (1 - σ) / (2 * max C 1 * L₁ * A * (2 / ε) * Pc) ≤ X * Q := by
  have hCp : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hden : 0 < 2 * max C 1 * L₁ * A * (2 / ε) * Pc :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos two_pos hCp) hL₁) hA) (div_pos two_pos hε)) hPc
  have hLX : 0 ≤ L₁ * X := mul_nonneg hL₁.le hX
  have hp : 0 ≤ L₁ * X * Lψ * Nk := mul_nonneg (mul_nonneg hLX hLψ0) hNk0
  have s1 : C * (L₁ * X * Lψ) * Nk ≤ max C 1 * (L₁ * X * Lψ * Nk) := by
    have := mul_le_mul_of_nonneg_right (le_max_left C 1) hp
    linarith
  have hAM : 0 ≤ A * (M / (ε / 2)) := mul_nonneg hA.le (div_nonneg hM0 (by linarith))
  have s2 : L₁ * X * Lψ * Nk ≤ L₁ * X * (A * (M / (ε / 2))) * M :=
    mul_le_mul (mul_le_mul_of_nonneg_left hLψ hLX) hNk hNk0 (mul_nonneg hLX hAM)
  have s3 := mul_le_mul_of_nonneg_left s2 hCp.le
  have e : max C 1 * (L₁ * X * (A * (M / (ε / 2))) * M) =
      max C 1 * L₁ * A * (2 / ε) * X * (M * M) := by ring
  rw [hMM] at e
  rw [div_le_iff₀ hden]
  linarith
private theorem div_le_mul_of_chain_caseB {L₁ X W D Nε Pc Q : ℝ} (hL₁ : 0 < L₁) (hX : 0 ≤ X) (hD : 0 < D)
    (hPc : 0 < Pc) (hS : L₁ ≤ W * X) (hW : W ≤ D * Nε) (hN : Nε ≤ Pc * Q) :
    L₁ / (D * Pc) ≤ X * Q := by
  rw [div_le_iff₀ (mul_pos hD hPc)]
  calc L₁ ≤ W * X := hS
    _ ≤ D * Nε * X := mul_le_mul_of_nonneg_right hW hX
    _ ≤ D * (Pc * Q) * X := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hD.le) hX
    _ = X * Q * (D * Pc) := by ring
end Formalism.ZeroFreeDirichlet
end
end

set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (hP : ProdCharExists) (hS : SameCharacterLFunctionOne) {C K CL : ℝ}
    (hKey : ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
      (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)),
      χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 → ψ ≠ 1 → IsProdChar χ₁ χ₂ ψ →
      ∀ σ : ℝ, 7 / 8 ≤ σ → σ < 1 →
        1 / 2 - C * ‖lamBq χ₁ χ₂ ψ‖ * ((q₁ * q₂ : ℕ) : ℝ) ^ (K * (1 - σ)) / (1 - σ) ≤ (Fbq χ₁ χ₂ ψ σ).re)
    (hL : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ‖DirichletCharacter.LFunction χ 1‖ ≤ CL * Real.log (3 * q))
    {ε : ℝ} (hε : 0 < ε) {q₁ : ℕ} [NeZero q₁] (χ₁ : DirichletCharacter ℂ q₁) (h1sq : χ₁ ^ 2 = 1)
    (h1ne : χ₁ ≠ 1) {σ : ℝ} (hσ78 : 7 / 8 ≤ σ) (hσ1 : σ < 1) (hKa : K * (1 - σ) ≤ ε / 2)
    (hneg : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ (q₁ * q)),
      χ ^ 2 = 1 → χ ≠ 1 → ψ ≠ 1 → IsProdChar χ₁ χ ψ → (Fbq χ₁ χ ψ σ).re ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
      c * (q : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  have h1σ : 0 < 1 - σ := by linarith
  have hL₁ : 0 < ‖DirichletCharacter.LFunction χ₁ 1‖ :=
    norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero h1ne)
  have hA : 0 < |CL| + 1 := by positivity
  have hq₁ : (1 : ℝ) ≤ q₁ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
  have hPc : 0 < ((3 : ℝ) * q₁) ^ ε := Real.rpow_pos_of_pos (by positivity) ε
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hD : 0 < (2 / (ε * Real.log 2) + 1) ^ 2 :=
    pow_pos (by have := div_pos two_pos (mul_pos hε hl2); linarith) 2
  have hCp : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hden : 0 < 2 * max C 1 * ‖DirichletCharacter.LFunction χ₁ 1‖ * (|CL| + 1) * (2 / ε) *
      ((3 : ℝ) * q₁) ^ ε :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos two_pos hCp) hL₁) hA) (div_pos two_pos hε)) hPc
  refine ⟨min ((1 - σ) / (2 * max C 1 * ‖DirichletCharacter.LFunction χ₁ 1‖ * (|CL| + 1) * (2 / ε) *
      ((3 : ℝ) * q₁) ^ ε))
    (‖DirichletCharacter.LFunction χ₁ 1‖ / ((2 / (ε * Real.log 2) + 1) ^ 2 * ((3 : ℝ) * q₁) ^ ε)),
    lt_min (div_pos h1σ hden) (div_pos hL₁ (mul_pos hD hPc)), ?_⟩
  intro q _ χ hsq hne
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hQ : 0 < (q : ℝ) ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  rw [Real.rpow_neg hq0, ← div_eq_mul_inv, div_le_iff₀ hQ]
  have hN : ((q₁ * q : ℕ) : ℝ) = (q₁ : ℝ) * q := by push_cast; ring
  have hN1 : (1 : ℝ) ≤ ((q₁ * q : ℕ) : ℝ) := by rw [hN]; nlinarith
  have hNε : ((q₁ * q : ℕ) : ℝ) ^ ε ≤ ((3 : ℝ) * q₁) ^ ε * (q : ℝ) ^ ε := by
    rw [hN, Real.mul_rpow (by linarith) hq0]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by linarith) (by linarith) hε.le) hQ.le
  obtain ⟨ψ, hψ⟩ := hP q₁ q χ₁ χ
  by_cases hψ1 : ψ = 1
  ·
    refine le_trans (min_le_right _ _) ?_
    exact div_le_mul_of_chain_caseB hL₁ (norm_nonneg _) hD hPc
      (hS q₁ q χ₁ χ h1ne hne (agree_coprime_of_product_principal χ₁ χ ψ hsq hψ hψ1))
      (card_primeFactors_add_one_sq_le_rpow hε (q₁ * q) (Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q))) hNε
  ·
    refine le_trans (min_le_left _ _) ?_
    have hk := hKey q₁ q χ₁ χ ψ h1sq hsq h1ne hne hψ1 hψ σ hσ78 hσ1
    have hn := hneg q χ ψ hsq hne hψ1 hψ
    have hmain : (1 - σ) / 2 ≤ C * (‖DirichletCharacter.LFunction χ₁ 1‖ * ‖DirichletCharacter.LFunction χ 1‖ *
        ‖DirichletCharacter.LFunction ψ 1‖) * ((q₁ * q : ℕ) : ℝ) ^ (K * (1 - σ)) := by
      have h2 : 1 / 2 ≤ C * ‖lamBq χ₁ χ ψ‖ * ((q₁ * q : ℕ) : ℝ) ^ (K * (1 - σ)) / (1 - σ) := by linarith
      rw [le_div_iff₀ h1σ] at h2
      have hlam : ‖lamBq χ₁ χ ψ‖ = ‖DirichletCharacter.LFunction χ₁ 1‖ * ‖DirichletCharacter.LFunction χ 1‖ *
          ‖DirichletCharacter.LFunction ψ 1‖ := by simp only [lamBq, norm_mul]
      rw [hlam] at h2
      linarith
    have h3N : (1 : ℝ) ≤ 3 * ((q₁ * q : ℕ) : ℝ) := by linarith
    have hM0 : 0 ≤ (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) := by positivity
    have hlogb : Real.log (3 * ((q₁ * q : ℕ) : ℝ)) ≤ (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) / (ε / 2) :=
      Real.log_le_rpow_div (by linarith) (by linarith)
    have hLψ : ‖DirichletCharacter.LFunction ψ 1‖ ≤
        (|CL| + 1) * ((3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) / (ε / 2)) := by
      calc ‖DirichletCharacter.LFunction ψ 1‖ ≤ CL * Real.log (3 * ((q₁ * q : ℕ) : ℝ)) := hL (q₁ * q) ψ hψ1
        _ ≤ (|CL| + 1) * Real.log (3 * ((q₁ * q : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self CL]) (Real.log_nonneg h3N)
        _ ≤ _ := mul_le_mul_of_nonneg_left hlogb hA.le
    have hNk : ((q₁ * q : ℕ) : ℝ) ^ (K * (1 - σ)) ≤ (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) :=
      (Real.rpow_le_rpow_of_exponent_le hN1 hKa).trans
        (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
    have hMM : (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) * (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) =
        ((3 : ℝ) * q₁) ^ ε * (q : ℝ) ^ ε := by
      rw [← Real.rpow_add (by linarith), add_halves, hN, ← mul_assoc, Real.mul_rpow (by positivity) hq0]
    exact div_le_mul_of_main_bound_caseA hε h1σ hL₁ (norm_nonneg _) hA (by positivity) (norm_nonneg _) hM0
      hmain hLψ hNk hMM hPc
end Formalism.ZeroFreeDirichlet
