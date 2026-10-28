-- Prove2me | solution 1 for DynamicOnlineLP.DLA.phase_sums
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:05:24.025022+00:00
-- url     : https://prove2.me/submissions/ed8aaaa3-8eba-46d2-a018-3838f96087ea

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_Algorithm

open DynamicOnlineLP.DLA in
theorem solution (n E : ℕ) (hn : 0 < n) (hE : 1 ≤ E) (hdiv : 2 ^ E ∣ n) :
    ∑ ℓ ∈ phases n E, (ℓ : ℝ) / (n : ℝ) = 1 - eps E ∧
      ∑ ℓ ∈ phases n E, slack n E ℓ * ((ℓ : ℝ) / (n : ℝ)) =
        eps E * ∑ ℓ ∈ phases n E, Real.sqrt ((ℓ : ℝ) / (n : ℝ)) ∧
      eps E * ∑ ℓ ∈ phases n E, Real.sqrt ((ℓ : ℝ) / (n : ℝ)) ≤ 2.5 * eps E := by
  set L := learnLen n E with hLdef
  have hL : L * 2 ^ E = n := by
    rw [hLdef]; unfold learnLen; exact Nat.div_mul_cancel hdiv
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h, zero_mul] at hL; omega
    · exact h
  have hnR : (n : ℝ) = (L : ℝ) * 2 ^ E := by rw [← hL]; push_cast; ring
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL0
  have hinj : Set.InjOn (fun r : ℕ => L * 2 ^ r) (Finset.range E : Set ℕ) := by
    intro r _ s _ h
    simp only at h
    exact Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_left hL0 h)
  have hph : phases n E = (Finset.range E).image (fun r : ℕ => L * 2 ^ r) := rfl
  have hterm : ∀ r : ℕ, (((L * 2 ^ r : ℕ) : ℝ)) / (n : ℝ) = (2 : ℝ) ^ r / 2 ^ E := by
    intro r
    rw [hnR]
    push_cast
    field_simp
  have hsum : ∀ f : ℝ → ℝ, ∑ ℓ ∈ phases n E, f ((ℓ : ℝ) / (n : ℝ)) =
      ∑ r ∈ Finset.range E, f ((2 : ℝ) ^ r / 2 ^ E) := by
    intro f
    rw [hph, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro r _
    rw [hterm r]
  have heps : eps E = 1 / (2 : ℝ) ^ E := by unfold eps; rw [one_div_pow]
  have h2E : (0 : ℝ) < 2 ^ E := by positivity
  have hepspos : 0 < eps E := by rw [heps]; positivity
  refine ⟨?_, ?_, ?_⟩
  · have := hsum (fun x => x)
    rw [this, ← Finset.sum_div, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1), heps]
    field_simp
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [hph, Finset.mem_image] at hℓ
    obtain ⟨r, _, rfl⟩ := hℓ
    have hx : 0 < (((L * 2 ^ r : ℕ) : ℝ)) / (n : ℝ) := by
      rw [hterm]; positivity
    unfold slack
    set x := (((L * 2 ^ r : ℕ) : ℝ)) / (n : ℝ) with hxdef
    have hnx : (n : ℝ) / ((L * 2 ^ r : ℕ) : ℝ) = x⁻¹ := by rw [hxdef, inv_div]
    rw [hnx, Real.sqrt_inv]
    have hs := Real.mul_self_sqrt hx.le
    have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    rw [mul_assoc]
    congr 1
    calc (Real.sqrt x)⁻¹ * x = (Real.sqrt x)⁻¹ * (Real.sqrt x * Real.sqrt x) := by rw [hs]
      _ = Real.sqrt x := by field_simp
  · have := hsum (fun x => Real.sqrt x)
    rw [this, mul_comm (2.5 : ℝ)]
    apply mul_le_mul_of_nonneg_left _ hepspos.le
    set q := Real.sqrt 2 with hq
    have hq14 : (1.4 : ℝ) ≤ q := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have hsp : ∀ r : ℕ, Real.sqrt ((2 : ℝ) ^ r) = q ^ r := by
      intro r
      rw [show (2 : ℝ) ^ r = (q ^ r) ^ 2 by
        rw [← pow_mul, mul_comm, pow_mul, hq, Real.sq_sqrt (by norm_num)],
        Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg 2) r)]
    have e : ∑ r ∈ Finset.range E, Real.sqrt ((2 : ℝ) ^ r / 2 ^ E) =
        (∑ r ∈ Finset.range E, q ^ r) / q ^ E := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _
      rw [Real.sqrt_div (by positivity), hsp, hsp]
    rw [e, geom_sum_eq (by linarith : q ≠ 1), div_div]
    have hqE : 0 < q ^ E := by positivity
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
