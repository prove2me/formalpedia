-- Prove2me | solution 1 for Erdos287.fixed_layer_neighbor_reduced_residue_class
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:17:18.474793+00:00
-- url     : https://prove2.me/submissions/f1cca82e-2cd5-4155-8f64-2b8a273c3dbd

import Mathlib

set_option autoImplicit false

/-- For a fixed layer coefficient, neighboring cofactor and sign,
the neighboring prime labels occupy a single reduced residue class. -/
theorem solution (p b a₀ q₀ : ℕ) (e : ℤ) (he : e = 1 ∨ e = -1)
    (h₀ : (a₀ : ℤ) * p = (b : ℤ) * q₀ + e) :
    p.Coprime b ∧ p.Coprime q₀ ∧
      ∀ a q : ℕ, (a : ℤ) * p = (b : ℤ) * q + e → q ≡ q₀ [MOD p] := by
  have hone (d : ℕ) (hd : (d : ℤ) ∣ e) : d = 1 := by
    have hd₁ : (d : ℤ) ∣ 1 := by
      rcases he with h | h
      · simpa only [h] using hd
      · simpa only [h, dvd_neg] using hd
    exact Nat.dvd_one.mp (by exact_mod_cast hd₁)
  have hcop (d : ℕ) (h₁ : (d : ℤ) ∣ (p : ℤ))
      (h₂ : (d : ℤ) ∣ (b : ℤ) * q₀) : d = 1 := by
    apply hone
    have hd := dvd_sub (dvd_mul_of_dvd_right h₁ (a₀ : ℤ)) h₂
    rwa [show (a₀ : ℤ) * p - (b : ℤ) * q₀ = e by linarith] at hd
  have hpb : p.Coprime b := hcop _ (by exact_mod_cast Nat.gcd_dvd_left p b)
    (dvd_mul_of_dvd_left (by exact_mod_cast Nat.gcd_dvd_right p b) (q₀ : ℤ))
  have hpq : p.Coprime q₀ := hcop _ (by exact_mod_cast Nat.gcd_dvd_left p q₀)
    (dvd_mul_of_dvd_right (by exact_mod_cast Nat.gcd_dvd_right p q₀) (b : ℤ))
  refine ⟨hpb, hpq, fun a q h => Nat.modEq_iff_dvd.mpr ?_⟩
  have hm : (p : ℤ) ∣ (b : ℤ) * ((q₀ : ℤ) - q) := by
    refine ⟨(a₀ : ℤ) - a, ?_⟩
    linear_combination h - h₀
  exact Int.dvd_of_dvd_mul_right_of_gcd_one hm (by simpa using hpb)

