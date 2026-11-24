-- Prove2me | solution 1 for FTheoryK3Tate.discOrder_I0star_general
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-22T11:10:59.628968+00:00
-- url     : https://prove2.me/submissions/db73d80a-fc19-47b1-b088-62ac260fbe5d

import Definitions.Def_FTheoryK3TateCore

open Polynomial

open FTheoryK3Tate

variable {k : Type*} [Field k]

theorem solution (f g : k[X]) (t₀ : k)
    (hf : (X - C t₀) ^ 2 ∣ f) (hg : (X - C t₀) ^ 3 ∣ g)
    (hred : 4 * ((taylor t₀ f).coeff 2) ^ 3 + 27 * ((taylor t₀ g).coeff 3) ^ 2 ≠ 0) :
    (Δ f g).rootMultiplicity t₀ = 6 := by
  let F := f /ₘ (X - C t₀) ^ 2
  let G := g /ₘ (X - C t₀) ^ 3
  have hF : (X - C t₀) ^ 2 * F = f := by
    have hmod : f %ₘ (X - C t₀) ^ 2 = 0 :=
      (modByMonic_eq_zero_iff_dvd ((monic_X_sub_C t₀).pow 2)).2 hf
    have h := modByMonic_add_div f ((X - C t₀) ^ 2)
    rwa [hmod, zero_add] at h
  have hG : (X - C t₀) ^ 3 * G = g := by
    have hmod : g %ₘ (X - C t₀) ^ 3 = 0 :=
      (modByMonic_eq_zero_iff_dvd ((monic_X_sub_C t₀).pow 3)).2 hg
    have h := modByMonic_add_div g ((X - C t₀) ^ 3)
    rwa [hmod, zero_add] at h
  have htX : taylor t₀ (X - C t₀) = X := by
    simp [taylor_apply, sub_comp]
  have ht2 : taylor t₀ ((X - C t₀) ^ 2) = X ^ 2 := by
    rw [pow_two, taylor_mul, htX, pow_two]
  have ht3 : taylor t₀ ((X - C t₀) ^ 3) = X ^ 3 := by
    rw [show (X - C t₀) ^ 3 = (X - C t₀) ^ 2 * (X - C t₀) by ring, taylor_mul, ht2, htX]
    ring
  have hc2 : (taylor t₀ f).coeff 2 = F.eval t₀ := by
    rw [← hF, taylor_mul, ht2, coeff_X_pow_mul (taylor t₀ F) 2 0, taylor_coeff_zero]
  have hc3 : (taylor t₀ g).coeff 3 = G.eval t₀ := by
    rw [← hG, taylor_mul, ht3, coeff_X_pow_mul (taylor t₀ G) 3 0, taylor_coeff_zero]
  have hQeval : (4 * F ^ 3 + 27 * G ^ 2).eval t₀ ≠ 0 := by
    have hq : (4 * F ^ 3 + 27 * G ^ 2).eval t₀
        = 4 * (F.eval t₀) ^ 3 + 27 * (G.eval t₀) ^ 2 := by simp
    rw [hq, ← hc2, ← hc3]
    exact hred
  have hQne : 4 * F ^ 3 + 27 * G ^ 2 ≠ 0 :=
    fun h0 => hQeval (by rw [h0]; simp)
  have hQ0 : (4 * F ^ 3 + 27 * G ^ 2).rootMultiplicity t₀ = 0 :=
    rootMultiplicity_eq_zero (fun hroot => hQeval hroot)
  have hΔeq : Δ f g = (X - C t₀) ^ 6 * (4 * F ^ 3 + 27 * G ^ 2) := by
    rw [Δ, ← hF, ← hG]
    ring
  rw [hΔeq, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 6 (monic_X_sub_C t₀).ne_zero) hQne),
    rootMultiplicity_X_sub_C_pow, hQ0, add_zero]

#check @solution
#print axioms solution
