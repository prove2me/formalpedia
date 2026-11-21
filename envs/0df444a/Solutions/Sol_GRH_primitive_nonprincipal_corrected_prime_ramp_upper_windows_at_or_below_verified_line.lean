-- Prove2me | solution 1 for GRH.primitive_nonprincipal_corrected_prime_ramp_upper_windows_at_or_below_verified_line
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T04:07:08.283186+00:00
-- url     : https://prove2.me/submissions/447f888e-cb23-44e0-be0a-78e965f5c7f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GRH_primitive_nonprincipal_integer_ramp_window_certificates
open Finset ArithmeticFunction Set
set_option maxHeartbeats 1200000

private theorem single_ramp_affine (n m : ℕ) (y : ℝ)
    (hy₀ : (m:ℝ) ≤ y) (hy₁ : y ≤ (m:ℝ)+1) :
    max (y/(n:ℝ)-1) 0 =
      ((m:ℝ)+1-y) * max ((m:ℝ)/(n:ℝ)-1) 0 +
      (y-(m:ℝ)) * max (((m:ℝ)+1)/(n:ℝ)-1) 0 := by
  by_cases hn : n = 0
  · subst n
    norm_num
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  by_cases hnm : n ≤ m
  · have hnm' : (n:ℝ) ≤ m := by exact_mod_cast hnm
    have h₀ : 0 ≤ y/(n:ℝ)-1 := by
      have := (le_div_iff₀ hnpos).2 (by linarith : 1*(n:ℝ) ≤ y)
      linarith
    have h₁ : 0 ≤ (m:ℝ)/(n:ℝ)-1 := by
      have := (le_div_iff₀ hnpos).2 (by linarith : 1*(n:ℝ) ≤ m)
      linarith
    have h₂ : 0 ≤ ((m:ℝ)+1)/(n:ℝ)-1 := by
      have := (le_div_iff₀ hnpos).2 (by linarith : 1*(n:ℝ) ≤ (m:ℝ)+1)
      linarith
    rw [max_eq_left h₀, max_eq_left h₁, max_eq_left h₂]
    ring
  · have hmn : (m:ℝ)+1 ≤ n := by exact_mod_cast (by omega : m+1 ≤ n)
    have h₀ : y/(n:ℝ)-1 ≤ 0 := by
      have := (div_le_iff₀ hnpos).2 (by linarith : y ≤ 1*(n:ℝ))
      linarith
    have h₁ : (m:ℝ)/(n:ℝ)-1 ≤ 0 := by
      have := (div_le_iff₀ hnpos).2 (by linarith : (m:ℝ) ≤ 1*(n:ℝ))
      linarith
    have h₂ : ((m:ℝ)+1)/(n:ℝ)-1 ≤ 0 := by
      have := (div_le_iff₀ hnpos).2 (by linarith : (m:ℝ)+1 ≤ 1*(n:ℝ))
      linarith
    rw [max_eq_right h₀, max_eq_right h₁, max_eq_right h₂]
    ring

private theorem ramp_integer_interpolation (a : ℕ → ℝ) (b y : ℝ) (hy : 0 ≤ y) :
    let R := fun x : ℝ => (∑ n ∈ range (⌊x⌋₊+1), a n * max (x/(n:ℝ)-1) 0) + x*b
    R y = ((⌊y⌋₊:ℝ)+1-y)*R (⌊y⌋₊:ℝ) +
      (y-(⌊y⌋₊:ℝ))*R ((⌊y⌋₊:ℝ)+1) := by
  dsimp only
  let m := ⌊y⌋₊
  have hlo : (m:ℝ) ≤ y := Nat.floor_le hy
  have hup : y ≤ (m:ℝ)+1 := le_of_lt (Nat.lt_floor_add_one y)
  have hf₀ : ⌊(m:ℝ)⌋₊ = m := Nat.floor_natCast m
  have hf₁ : ⌊(m:ℝ)+1⌋₊ = m+1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.floor_natCast]
  change (∑ n ∈ range (m+1), a n * max (y/(n:ℝ)-1) 0) + y*b = _
  change _ = ((m:ℝ)+1-y)*
      ((∑ n ∈ range (⌊(m:ℝ)⌋₊+1), a n * max ((m:ℝ)/(n:ℝ)-1) 0)+(m:ℝ)*b) +
    (y-(m:ℝ))*
      ((∑ n ∈ range (⌊(m:ℝ)+1⌋₊+1), a n * max (((m:ℝ)+1)/(n:ℝ)-1) 0)+((m:ℝ)+1)*b)
  rw [hf₀, hf₁, sum_range_succ (fun n => a n * max (((m:ℝ)+1)/(n:ℝ)-1) 0) (m+1)]
  have hlast : max (((m:ℝ)+1)/((m+1:ℕ):ℝ)-1) 0 = 0 := by
    rw [Nat.cast_add, Nat.cast_one, div_self (by positivity : (m:ℝ)+1 ≠ 0)]
    norm_num
  rw [hlast, mul_zero, add_zero]
  have heq : (∑ n ∈ range (m+1), a n * max (y/(n:ℝ)-1) 0) =
      ((m:ℝ)+1-y)*(∑ n ∈ range (m+1), a n * max ((m:ℝ)/(n:ℝ)-1) 0) +
      (y-(m:ℝ))*(∑ n ∈ range (m+1), a n * max (((m:ℝ)+1)/(n:ℝ)-1) 0) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    rw [single_ramp_affine n m y hlo hup]
    ring
  rw [heq]
  ring

private theorem ramp_bound_from_integer_knots (a : ℕ → ℝ) (b θ C y : ℝ)
    (hθ : 0 ≤ θ) (hC : 0 ≤ C) (hy : 1 ≤ y)
    (hlo : (∑ n ∈ range (⌊y⌋₊+1), a n * max ((⌊y⌋₊:ℝ)/(n:ℝ)-1) 0) +
      (⌊y⌋₊:ℝ)*b ≤ C*(⌊y⌋₊:ℝ)^θ)
    (hhi : (∑ n ∈ range (⌊y⌋₊+1+1), a n * max (((⌊y⌋₊:ℝ)+1)/(n:ℝ)-1) 0) +
      ((⌊y⌋₊:ℝ)+1)*b ≤ C*((⌊y⌋₊:ℝ)+1)^θ) :
    (∑ n ∈ range (⌊y⌋₊+1), a n * max (y/(n:ℝ)-1) 0) + y*b ≤
      (C*2^θ)*y^θ := by
  let R := fun x : ℝ => (∑ n ∈ range (⌊x⌋₊+1), a n * max (x/(n:ℝ)-1) 0)+x*b
  have h₀ : R (⌊y⌋₊:ℝ) ≤ C*((⌊y⌋₊:ℝ)+1)^θ := by
    dsimp [R]
    rw [Nat.floor_natCast]
    exact hlo.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) hθ) hC)
  have h₁ : R ((⌊y⌋₊:ℝ)+1) ≤ C*((⌊y⌋₊:ℝ)+1)^θ := by
    dsimp [R]
    convert hhi using 1
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.floor_natCast]
  have hlow : (⌊y⌋₊:ℝ) ≤ y := Nat.floor_le (by linarith)
  have hhigh : y ≤ (⌊y⌋₊:ℝ)+1 := le_of_lt (Nat.lt_floor_add_one y)
  have hI := ramp_integer_interpolation a b y (by linarith)
  change R y = _ at hI
  change R y ≤ _
  calc
    R y = ((⌊y⌋₊:ℝ)+1-y)*R (⌊y⌋₊:ℝ) +
        (y-(⌊y⌋₊:ℝ))*R ((⌊y⌋₊:ℝ)+1) := hI
    _ ≤ ((⌊y⌋₊:ℝ)+1-y)*(C*((⌊y⌋₊:ℝ)+1)^θ) +
        (y-(⌊y⌋₊:ℝ))*(C*((⌊y⌋₊:ℝ)+1)^θ) :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ (by linarith))
        (mul_le_mul_of_nonneg_left h₁ (by linarith))
    _ = C*((⌊y⌋₊:ℝ)+1)^θ := by ring
    _ ≤ C*(2*y)^θ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) hθ) hC
    _ = (C*2^θ)*y^θ := by rw [Real.mul_rpow (by norm_num) (by linarith)]; ring

theorem solution :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ θ : ℝ, 1/2 < θ → θ ≤ (0.8749570698:ℝ) → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
        ∀ X : ℝ, 1 ≤ X → ∃ Y : ℝ, X ≤ Y ∧ ∀ y ∈ Icc Y (Y^(1+δ)),
          (∑ n ∈ range (⌊y⌋₊+1), vonMangoldt n * (χ (n:ZMod q)).re * max (y/(n:ℝ)-1) 0) +
              y * (deriv χ.LFunction 1 / χ.LFunction 1).re ≤ C*y^θ := by
  intro q _ χ hprim hχ θ hhalf hcap
  obtain ⟨δ, C, hδ, hC, hknots⟩ :=
    GRH.primitive_nonprincipal_integer_ramp_window_certificates q χ hprim hχ θ hhalf hcap
  refine ⟨δ, C*2^θ, hδ, mul_nonneg hC (Real.rpow_nonneg (by norm_num) _), ?_⟩
  intro X hX
  obtain ⟨M, hMX, hM₁, hM⟩ := hknots ⌈X⌉₊
  have hXM : X ≤ (M:ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast hMX)
  refine ⟨(M:ℝ), hXM, ?_⟩
  intro y hy
  have hy₁ : 1 ≤ y := hX.trans (hXM.trans hy.1)
  have hlow : M ≤ ⌊y⌋₊ := Nat.le_floor hy.1
  have hhigh : ⌊y⌋₊ ≤ ⌊(M:ℝ)^(1+δ)⌋₊ := Nat.floor_le_floor hy.2
  have hk₀ := hM ⌊y⌋₊ (Finset.mem_Icc.mpr ⟨hlow, by omega⟩)
  have hk₁ := hM (⌊y⌋₊+1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  simpa only [Nat.cast_add, Nat.cast_one] using
    ramp_bound_from_integer_knots
      (fun n => vonMangoldt n * (χ (n:ZMod q)).re)
      (deriv χ.LFunction 1 / χ.LFunction 1).re θ C y
      (by linarith : 0 ≤ θ) hC hy₁ hk₀ (by simpa only [Nat.cast_add, Nat.cast_one] using hk₁)
