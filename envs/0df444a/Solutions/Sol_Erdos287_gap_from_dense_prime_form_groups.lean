-- Prove2me | solution 1 for Erdos287.gap_from_dense_prime_form_groups
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T03:20:24.473021+00:00
-- url     : https://prove2.me/submissions/2b745fe0-51ea-437b-920f-cdf583ddd37c

import Mathlib
import Theorems.Thm_Erdos287_distance_packing_bound
import Theorems.Thm_Erdos287_omission_mass_extends_pair_band
import Theorems.Thm_Erdos287_prime_power_cofactor_log_bound

open Finset

set_option autoImplicit false

/-- Dense occupied groups of prime affine forms give two adjacent absent denominators. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (N u v t : ℕ) (S : Finset ℕ) (a : ℕ → ℕ) (hu : 0 < u) (hv : 2 * u ≤ v + 2)
    (hS : ∀ s ∈ S, s < N) (hdensity : u * (N + v) < (u + v) * S.card)
    (hprime : ∀ s ∈ S, Nat.Prime (a s * t + 1))
    (hlarge : ∀ s ∈ S, let p := a s * t + 1; let B := f (k - 1) / p
      Real.log B + Chebyshev.psi B < Real.log p)
    (hpairs : ∀ s ∈ S, ∀ r ∈ S, u ≤ r - s → r - s ≤ v →
      let d := a r - a s
      let x := (a s / d) * (a r * t + 1)
      a s < a r ∧ d ∣ a s ∧ x + 1 ≤ f (k - 1) ∧ (f (k - 1) : ℝ) < Real.exp 1 * x) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  classical
  have hpick : ∃ s ∈ S, ∃ r ∈ S, u ≤ r - s ∧ r - s ≤ v := by
    by_contra! havoid
    have hbound := Erdos287.distance_packing_bound N u v S hu hv hS havoid
    exact hdensity.not_ge hbound
  obtain ⟨s, hs, r, hr, hd1, hd2⟩ := hpick
  let M := f (k - 1)
  let p := a s * t + 1
  let q := a r * t + 1
  let d := a r - a s
  let c := a s / d
  let x := c * q
  have ⟨hal, hdvd, hlo, hhi⟩ : a s < a r ∧ d ∣ a s ∧ x + 1 ≤ M ∧ (M : ℝ) < Real.exp 1 * x :=
    hpairs s hs r hr hd1 hd2
  change x + 1 ≤ M at hlo
  change (M : ℝ) < Real.exp 1 * x at hhi
  have hcoef : c * d = a s := Nat.div_mul_cancel hdvd
  have hnext : (c + 1) * d = a r := by
    rw [add_mul, one_mul, hcoef]
    dsimp [d]
    omega
  have hx1 : (c + 1) * p = x + 1 := by
    calc
      (c + 1) * p = (c + 1) * (c * d * t + 1) := by rw [hcoef]
      _ = c * ((c + 1) * d * t + 1) + 1 := by ring
      _ = x + 1 := by rw [hnext]
  have hmiss_prime (s : ℕ) (hs : s ∈ S) (i : ℕ) (hi : i < k) : ¬ (a s * t + 1) ∣ f i := by
    intro hdiv
    have hbound := Erdos287.prime_power_cofactor_log_bound k hk f hf1 hmono hsum
      (a s * t + 1) 1 i (hprime s hs) le_rfl hi (by simpa using hdiv)
    simp only [pow_one] at hbound
    exact (hlarge s hs).not_ge hbound
  have hmiss : ∀ i, i < k → f i ∉ ({x, x + 1} : Finset ℕ) := by
    intro i hi hmem
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with h | h
    · apply hmiss_prime r hr i hi
      rw [h]
      exact dvd_mul_left q c
    · apply hmiss_prime s hs i hi
      rw [h, ← hx1]
      exact dvd_mul_left p (c + 1)
  have hMp : 0 < M := by have := hf1 (k - 1) (by omega); omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMp
  have hx : 0 < x := by
    by_contra! h
    have hzero : x = 0 := by omega
    simp only [hzero, Nat.cast_zero, mul_zero] at hhi
    exact hMR.not_gt hhi
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hlog : Real.log ((M : ℝ) / x) < 1 := by
    have h := Real.log_lt_log (div_pos hMR hxR) ((div_lt_iff₀ hxR).mpr hhi)
    rwa [Real.log_exp] at h
  refine Erdos287.omission_mass_extends_pair_band k hk f hmono hsum x hx hlo {x, x + 1}
    ?_ hmiss (by simp) (by simp) ?_
  · intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl <;> omega
  · exact hlog.trans_le (by
      have h : (0 : ℝ) ≤ ∑ n ∈ ({x, x + 1} : Finset ℕ).erase x, (1 : ℝ) / n :=
        sum_nonneg (fun n _ => div_nonneg zero_le_one (Nat.cast_nonneg n))
      linarith)

