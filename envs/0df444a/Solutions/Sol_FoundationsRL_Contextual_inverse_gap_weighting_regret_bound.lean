-- Prove2me | solution 1 for FoundationsRL.Contextual.inverse_gap_weighting_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T05:13:22.662149+00:00
-- url     : https://prove2.me/submissions/176e26e4-38e8-4283-bf6e-d5c02e7ab0ae

import Mathlib
import Definitions.Def_FoundationsRL_Contextual_IsIGW



namespace FoundationsRL.Contextual

lemma igw_amgm (c x : ℝ) (hc : 0 < c) : x ≤ c / 2 * x ^ 2 + 1 / (2 * c) := by
  have key : c / 2 * x ^ 2 + 1 / (2 * c) - x = (c * x - 1) ^ 2 / (2 * c) := by
    field_simp
    ring
  have := div_nonneg (sq_nonneg (c * x - 1)) (by positivity : (0:ℝ) ≤ 2 * c)
  linarith

theorem igw_main {A : ℕ} (fhat fstar : Fin A → ℝ) (γ : ℝ)
    (hγ : 0 < γ) (bstar : Fin A) (pistar : Fin A)
    (p : Fin A → ℝ) (hp : IsIGW A fhat γ bstar p) :
    fstar pistar - ∑ π, p π * fstar π ≤ (A : ℝ) / γ + γ * ∑ π, p π * (fhat π - fstar π) ^ 2 := by
  obtain ⟨lam, ⟨hlam1, hlamA⟩, hpdef⟩ := hp.lam_spec
  have hsum := hp.sum_one
  have hnn := hp.nonneg
  set Δ : Fin A → ℝ := fun π => fhat bstar - fhat π with hΔ
  set e : Fin A → ℝ := fun π => fhat π - fstar π with he
  have hpdef' : ∀ π, p π = 1 / (lam + 2 * γ * Δ π) := hpdef
  have hΔnn : ∀ π, 0 ≤ Δ π := fun π => by simp only [hΔ]; linarith [hp.greedy π]
  have hden : ∀ π, 0 < lam + 2 * γ * Δ π := fun π => by
    have := hΔnn π; positivity
  -- the regret decomposition
  have hid : fstar pistar - ∑ π, p π * fstar π
      = ∑ π, p π * Δ π + ∑ π, p π * e π - Δ pistar - e pistar := by
    have h1 : ∑ π, p π * Δ π + ∑ π, p π * e π = fhat bstar - ∑ π, p π * fstar π := by
      rw [← Finset.sum_add_distrib]
      have : ∀ π, p π * Δ π + p π * e π = p π * fhat bstar - p π * fstar π := fun π => by
        simp only [hΔ, he]; ring
      simp_rw [this]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
    rw [h1]
    simp only [hΔ, he]
    ring
  -- exploitation term
  have hterm : ∀ π, p π * Δ π ≤ 1 / (2 * γ) := by
    intro π
    rw [hpdef' π, one_div_mul_eq_div, div_le_div_iff₀ (hden π) (by positivity)]
    nlinarith [hΔnn π]
  have hA : 1 ≤ A := Fin.pos bstar
  have h1 : ∑ π, p π * Δ π ≤ ((A : ℝ) - 1) / (2 * γ) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ bstar)]
    have hb : p bstar * Δ bstar = 0 := by simp [hΔ]
    rw [hb, add_zero]
    calc ∑ π ∈ Finset.univ.erase bstar, p π * Δ π
        ≤ (Finset.univ.erase bstar).card • (1 / (2 * γ)) :=
          Finset.sum_le_card_nsmul _ _ _ (fun π _ => hterm π)
      _ = ((A : ℝ) - 1) / (2 * γ) := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_sub hA, Nat.cast_one]
          ring
  -- estimation error on the played actions
  have h2 : ∑ π, p π * e π ≤ γ / 2 * ∑ π, p π * e π ^ 2 + 1 / (2 * γ) := by
    have hpt : ∀ π, p π * e π ≤ γ / 2 * (p π * e π ^ 2) + 1 / (2 * γ) * p π := by
      intro π
      have := mul_le_mul_of_nonneg_left (igw_amgm γ (e π) hγ) (hnn π)
      have e2 : p π * (γ / 2 * e π ^ 2 + 1 / (2 * γ)) =
          γ / 2 * (p π * e π ^ 2) + 1 / (2 * γ) * p π := by ring
      linarith
    calc ∑ π, p π * e π ≤ ∑ π, (γ / 2 * (p π * e π ^ 2) + 1 / (2 * γ) * p π) :=
          Finset.sum_le_sum fun π _ => hpt π
      _ = γ / 2 * ∑ π, p π * e π ^ 2 + 1 / (2 * γ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum, mul_one]
  -- estimation error at the optimal action
  have hpstar : 0 < p pistar := by rw [hpdef' pistar]; exact one_div_pos.mpr (hden pistar)
  have h3 : -e pistar - Δ pistar ≤ γ / 2 * (p pistar * e pistar ^ 2) + lam / (2 * γ) := by
    have ham := igw_amgm (γ * p pistar) (-e pistar) (mul_pos hγ hpstar)
    have hne : lam + 2 * γ * Δ pistar ≠ 0 := (hden pistar).ne'
    have hinv : 1 / (2 * (γ * p pistar)) = lam / (2 * γ) + Δ pistar := by
      rw [hpdef' pistar]
      field_simp
    rw [hinv, neg_sq] at ham
    have e3 : γ * p pistar / 2 * e pistar ^ 2 = γ / 2 * (p pistar * e pistar ^ 2) := by ring
    linarith
  have h4 : p pistar * e pistar ^ 2 ≤ ∑ π, p π * e π ^ 2 :=
    Finset.single_le_sum (f := fun π => p π * e π ^ 2)
      (fun π _ => mul_nonneg (hnn π) (sq_nonneg _)) (Finset.mem_univ pistar)
  have hlam : lam / (2 * γ) ≤ (A : ℝ) / (2 * γ) := div_le_div_of_nonneg_right hlamA (by positivity)
  have hA2 : (A : ℝ) / γ = ((A : ℝ) - 1) / (2 * γ) + 1 / (2 * γ) + (A : ℝ) / (2 * γ) := by
    field_simp
    ring
  have h4' : γ / 2 * (p pistar * e pistar ^ 2) ≤ γ / 2 * ∑ π, p π * e π ^ 2 :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  rw [hid]
  show _ ≤ (A : ℝ) / γ + γ * ∑ π, p π * e π ^ 2
  linarith

end FoundationsRL.Contextual

open FoundationsRL.Contextual

theorem solution {A : ℕ} (fhat fstar : Fin A → ℝ) (γ : ℝ)
    (hγ : 0 < γ) (bstar : Fin A) (pistar : Fin A) (hpistar : ∀ π, fstar π ≤ fstar pistar)
    (p : Fin A → ℝ) (hp : IsIGW A fhat γ bstar p) :
    fstar pistar - ∑ π, p π * fstar π ≤ (A : ℝ) / γ + γ * ∑ π, p π * (fhat π - fstar π) ^ 2 := by
  exact igw_main fhat fstar γ hγ bstar pistar p hp
