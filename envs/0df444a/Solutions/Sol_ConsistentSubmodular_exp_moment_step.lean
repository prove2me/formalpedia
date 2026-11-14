-- Prove2me | solution 1 for ConsistentSubmodular.exp_moment_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:30:19.816194+00:00
-- url     : https://prove2.me/submissions/3f636649-1009-45aa-839d-8f7e1e7ff9b2

import Mathlib

section

open scoped BigOperators

theorem solution {lam p δ d : ℝ} (hp0 : 0 ≤ p)
    (hδ0 : 0 ≤ δ) (hδd : δ ≤ d) (hd1 : d ≤ 1) :
    (1 - p) + p * Real.exp (-lam * d + (δ - d) * (Real.exp (-lam) - 1)) ≤
      Real.exp (p * δ * (Real.exp (-lam) - 1)) := by
  have hd0 : 0 ≤ d := hδ0.trans hδd
  have hlow : 1 - lam ≤ Real.exp (-lam) := Real.one_sub_le_exp_neg lam
  have hy : Real.exp (-lam * d + (δ - d) * (Real.exp (-lam) - 1)) ≤
      1 + δ * (Real.exp (-lam) - 1) := by
    rcases eq_or_lt_of_le hd0 with hd | hd
    · have hδ : δ = 0 := le_antisymm (by rw [hd]; exact hδd) hδ0
      rw [hδ, ← hd]
      simp
    · set t := Real.exp (-lam) - 1 with htdef
      set θ := δ / d with hθ
      have hθ0 : 0 ≤ θ := div_nonneg hδ0 hd0
      have hθ1 : θ ≤ 1 := (div_le_one hd).mpr hδd
      have hδθ : δ = θ * d := by rw [hθ]; field_simp
      have hcomb : -lam * d + (δ - d) * t = (1 - θ) * (-lam * d - d * t) + θ * (-lam * d) := by
        rw [hδθ]; ring
      have hconv := convexOn_exp.2 (Set.mem_univ (-lam * d - d * t)) (Set.mem_univ (-lam * d))
        (sub_nonneg.mpr hθ1) hθ0 (by ring)
      simp only [smul_eq_mul] at hconv
      have h1 : Real.exp (-lam * d - d * t) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        nlinarith [mul_nonneg hd0 (show 0 ≤ lam + t by linarith)]
      have h2 : Real.exp (-lam * d) ≤ 1 + d * t := by
        have hc := convexOn_exp.2 (Set.mem_univ (-lam)) (Set.mem_univ (0 : ℝ)) hd0
          (sub_nonneg.mpr hd1) (by ring)
        simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hc
        have he : -lam * d = d * -lam := by ring
        rw [he]
        linarith
      rw [hcomb]
      calc Real.exp ((1 - θ) * (-lam * d - d * t) + θ * (-lam * d))
          ≤ (1 - θ) * Real.exp (-lam * d - d * t) + θ * Real.exp (-lam * d) := hconv
        _ ≤ (1 - θ) * 1 + θ * (1 + d * t) := by
          nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hθ1),
            mul_le_mul_of_nonneg_left h2 hθ0]
        _ = 1 + δ * t := by rw [hδθ]; ring
  have hmain : (1 - p) + p * Real.exp (-lam * d + (δ - d) * (Real.exp (-lam) - 1)) ≤
      1 + p * δ * (Real.exp (-lam) - 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hy hp0]
  exact hmain.trans (by linarith [Real.add_one_le_exp (p * δ * (Real.exp (-lam) - 1))])

end
