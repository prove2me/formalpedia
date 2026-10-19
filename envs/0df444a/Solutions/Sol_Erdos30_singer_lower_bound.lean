-- Prove2me | solution 1 for Erdos30.singer_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T07:44:56.521575+00:00
-- url     : https://prove2.me/submissions/daca9473-a79e-4310-ac32-89a3ff09a797

import Mathlib
import Definitions.Def_Erdos30Basic
import Theorems.Thm_Erdos30_singer_construction
import Theorems.Thm_ArtinPrimitiveRoots_psi_prime_number_theorem

section

open Finset Real Filter Topology

namespace LET

/-- `log x ^ (k+1) ≤ C √x` for `x ≥ 1`. -/
lemma logpow_le_sqrt (k : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    Real.log x ^ (k + 1) ≤ (2 * (k + 1 : ℝ)) ^ (k + 1) * √x := by
  have hε : (0:ℝ) < 1 / (2 * (k + 1)) := by positivity
  have h := Real.log_le_rpow_div (by linarith : (0:ℝ) ≤ x) hε
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2 : Real.log x ≤ 2 * (k + 1) * x ^ (1 / (2 * (k + 1 : ℝ))) := by
    rw [div_div_eq_mul_div, div_one] at h; linarith
  calc Real.log x ^ (k + 1) ≤ (2 * (k + 1) * x ^ (1 / (2 * (k + 1 : ℝ)))) ^ (k + 1) :=
        pow_le_pow_left₀ hl h2 _
    _ = (2 * (k + 1 : ℝ)) ^ (k + 1) * (x ^ (1 / (2 * (k + 1 : ℝ)))) ^ (k + 1) := by rw [mul_pow]
    _ = (2 * (k + 1 : ℝ)) ^ (k + 1) * √x := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Real.sqrt_eq_rpow]
        congr 1; push_cast; field_simp

lemma log_floor_ge (x : ℝ) (hx : 2 ≤ x) : Real.log x / 2 ≤ Real.log (⌊x⌋₊ : ℝ) := by
  have hX : (2:ℝ) ≤ ⌊x⌋₊ := by
    have : (2:ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    exact_mod_cast this
  have hX2 : x / 2 ≤ ⌊x⌋₊ := by
    have := Nat.lt_floor_add_one x; linarith
  rcases le_or_gt 4 x with h4 | h4
  · have h1 : Real.log (x / 2) ≤ Real.log ⌊x⌋₊ := Real.log_le_log (by linarith) hX2
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) h4
    have e : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  · have h1 : Real.log 2 ≤ Real.log ⌊x⌋₊ := Real.log_le_log (by norm_num) hX
    have : Real.log x ≤ Real.log 4 := Real.log_le_log (by linarith) h4.le
    have e : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    linarith

/-- Chebyshev θ with a power-of-log error term, for all `x ≥ 2`. -/
theorem theta_bound (A : ℕ) (hA : 1 ≤ A) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
    |Chebyshev.theta x - x| ≤ C * x / Real.log x ^ A := by
  obtain ⟨C0, hC0⟩ := ArtinPrimitiveRoots.psi_prime_number_theorem (A : ℝ) (by exact_mod_cast hA)
  set K := (2 * (A + 1 : ℝ)) ^ (A + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨|C0| * 2 ^ A + 2 * K + K / Real.log 2, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlx0 : 0 < Real.log x := by linarith
  have hLA : 0 < Real.log x ^ A := by positivity
  set X := ⌊x⌋₊ with hXdef
  have hX2 : 2 ≤ X := Nat.le_floor (by exact_mod_cast hx)
  have hXr : (2:ℝ) ≤ X := by exact_mod_cast hX2
  have hXx : (X:ℝ) ≤ x := Nat.floor_le hx0.le
  have hxX : x < X + 1 := Nat.lt_floor_add_one x
  have hlX := log_floor_ge x hx
  have hlX0 : 0 < Real.log (X:ℝ) := Real.log_pos (by linarith)
  -- psi part
  have hpsi : |Chebyshev.psi x - X| ≤ |C0| * 2 ^ A * x / Real.log x ^ A := by
    have h := hC0 X hX2
    have hr : Real.log (X:ℝ) ^ (-(A:ℝ)) = (Real.log (X:ℝ) ^ A)⁻¹ := by
      rw [Real.rpow_neg hlX0.le, Real.rpow_natCast]
    rw [hr] at h
    have e : Chebyshev.psi x = ∑ n ∈ Ioc 0 X, ArithmeticFunction.vonMangoldt n := rfl
    rw [e]
    refine h.trans ?_
    have h1 : (Real.log x / 2) ^ A ≤ Real.log (X:ℝ) ^ A := pow_le_pow_left₀ (by positivity) hlX A
    rw [div_pow] at h1
    have h2 : (X:ℝ) * (Real.log (X:ℝ) ^ A)⁻¹ ≤ 2 ^ A * x / Real.log x ^ A := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hLA]
      have h1' : Real.log x ^ A ≤ 2 ^ A * Real.log (X:ℝ) ^ A := by
        rw [div_le_iff₀ (by positivity)] at h1; linarith
      calc (X:ℝ) * Real.log x ^ A ≤ x * Real.log x ^ A := by gcongr
        _ ≤ x * (2 ^ A * Real.log (X:ℝ) ^ A) := by gcongr
        _ = _ := by ring
    calc C0 * (X * (Real.log (X:ℝ) ^ A)⁻¹) ≤ |C0| * (X * (Real.log (X:ℝ) ^ A)⁻¹) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C0| * (2 ^ A * x / Real.log x ^ A) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = _ := by ring
  -- psi - theta
  have hpt : |Chebyshev.theta x - Chebyshev.psi x| ≤ 2 * K * x / Real.log x ^ A := by
    have h1 := Chebyshev.psi_sub_theta_le (by linarith : (1:ℝ) ≤ x)
    have h2 := Chebyshev.theta_le_psi x
    have h3 := logpow_le_sqrt A x (by linarith)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    refine h1.trans ?_
    rw [le_div_iff₀ hLA]
    have hs : √x * √x = x := Real.mul_self_sqrt hx0.le
    calc 2 * √x * Real.log x * Real.log x ^ A = 2 * √x * Real.log x ^ (A + 1) := by ring
      _ ≤ 2 * √x * (K * √x) := by gcongr
      _ = 2 * K * (√x * √x) := by ring
      _ = 2 * K * x := by rw [hs]
  -- floor part
  have hfl : |(X:ℝ) - x| ≤ K / Real.log 2 * x / Real.log x ^ A := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have h3 := logpow_le_sqrt A x (by linarith)
    have hsx : √x ≤ x := by
      have h1 : 1 ≤ √x := Real.one_le_sqrt.mpr (by linarith)
      nlinarith [Real.mul_self_sqrt hx0.le]
    have : Real.log x ^ A * Real.log 2 ≤ K * x := by
      calc Real.log x ^ A * Real.log 2 ≤ Real.log x ^ A * Real.log x := by gcongr
        _ = Real.log x ^ (A + 1) := by ring
        _ ≤ K * √x := h3
        _ ≤ K * x := by gcongr
    have key : 1 ≤ K / Real.log 2 * x / Real.log x ^ A := by
      rw [le_div_iff₀ hLA, div_mul_eq_mul_div, le_div_iff₀ hl2]; linarith
    linarith
  calc |Chebyshev.theta x - x| = |(Chebyshev.theta x - Chebyshev.psi x) + (Chebyshev.psi x - X) + (X - x)| := by ring_nf
    _ ≤ |Chebyshev.theta x - Chebyshev.psi x| + |Chebyshev.psi x - X| + |(X:ℝ) - x| := abs_add_three _ _ _
    _ ≤ 2 * K * x / Real.log x ^ A + |C0| * 2 ^ A * x / Real.log x ^ A + K / Real.log 2 * x / Real.log x ^ A := by
        gcongr
    _ = _ := by ring

end LET

end

section

namespace SGAux
open Erdos30 Filter

lemma h_mono {M N : ℕ} (hMN : M ≤ N) : h M ≤ h N := by
  unfold h maxSidonSubsetCard
  apply Finset.sup_mono
  apply Finset.filter_subset_filter
  exact Finset.powerset_mono.mpr (Finset.Icc_subset_Icc le_rfl hMN)

lemma prime_between (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ a * x < p ∧ (p : ℝ) ≤ b * x := by
  obtain ⟨C, hC0, hC⟩ := LET.theta_bound 1 le_rfl
  set K := C * (a + b) / (b - a) with hK
  filter_upwards [eventually_ge_atTop (2 / a), eventually_ge_atTop (Real.exp (K + 1) / a)]
    with x hx1 hx2
  have hax : 2 ≤ a * x := by rwa [div_le_iff₀' ha] at hx1
  have hax2 : Real.exp (K + 1) ≤ a * x := by rwa [div_le_iff₀' ha] at hx2
  have hx0 : 0 < x := by nlinarith
  have hbx : a * x ≤ b * x := by nlinarith
  have hlog : K + 1 ≤ Real.log (a * x) := by
    rw [← Real.log_exp (K + 1)]; exact Real.log_le_log (Real.exp_pos _) hax2
  by_contra hno
  push Not at hno
  have heq : Chebyshev.theta (b * x) = Chebyshev.theta (a * x) := by
    unfold Chebyshev.theta
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hp0, hpb⟩, hp⟩
      refine ⟨⟨hp0, ?_⟩, hp⟩
      by_contra hlt
      push Not at hlt
      have h1 : a * x < p := by
        have := Nat.lt_floor_add_one (a * x)
        have : ((⌊a * x⌋₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hlt
        push_cast at this; linarith
      have h2 : (p : ℝ) ≤ b * x := (Nat.le_floor_iff (by linarith)).mp hpb
      exact absurd h2 (not_le.mpr (hno p hp h1))
    · rintro ⟨⟨hp0, hpa⟩, hp⟩
      exact ⟨⟨hp0, hpa.trans (Nat.floor_le_floor hbx)⟩, hp⟩
  have hA := hC (a * x) hax
  have hB := hC (b * x) (by linarith)
  rw [pow_one] at hA hB
  have hla : 0 < Real.log (a * x) := Real.log_pos (by linarith)
  have hlb : Real.log (a * x) ≤ Real.log (b * x) := Real.log_le_log (by linarith) hbx
  have hB' : C * (b * x) / Real.log (b * x) ≤ C * (b * x) / Real.log (a * x) :=
    div_le_div_of_nonneg_left (mul_nonneg hC0 (by linarith)) hla hlb
  rw [heq] at hB
  have e1 := (abs_le.mp hA).2
  have e2 := (abs_le.mp hB).1
  have key : (b - a) * x ≤ C * (a + b) * x / Real.log (a * x) := by
    have : C * (a * x) / Real.log (a * x) + C * (b * x) / Real.log (a * x)
        = C * (a + b) * x / Real.log (a * x) := by field_simp
    linarith
  rw [le_div_iff₀ hla] at key
  have hba : 0 < b - a := by linarith
  have hK' : K * (b - a) = C * (a + b) := by rw [hK]; field_simp
  have : (b - a) * x * (K + 1) ≤ (b - a) * x * Real.log (a * x) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  nlinarith

theorem main : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (1 - ε) * Real.sqrt N ≤ (h N : ℝ) := by
  intro ε hε
  rcases le_or_gt 1 ε with h1 | h1
  · exact Eventually.of_forall fun N => le_trans
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)
  set a := 1 - ε
  set b := 1 - ε / 2
  have ha : 0 < a := by simp only [a]; linarith
  have hab : a < b := by simp only [a, b]; linarith
  have hb1 : b < 1 := by simp only [b]; linarith
  have hs : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ s : ℝ in atTop, (∃ p : ℕ, p.Prime ∧ a * s < p ∧ (p : ℝ) ≤ b * s) ∧
      1 / (1 - b) ≤ s := (prime_between a b ha hab).and (eventually_ge_atTop _)
  filter_upwards [hs.eventually hev] with N ⟨⟨p, hp, hp1, hp2⟩, hs1⟩
  set s := Real.sqrt N with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have h1b : 0 < 1 - b := by linarith
  have hs1' : 1 ≤ (1 - b) * s := by rwa [div_le_iff₀' h1b] at hs1
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hpN : p ^ 2 + p + 1 ≤ N := by
    have hb0 : 0 < b := by linarith
    have h2 : (p : ℝ) ^ 2 ≤ (b * s) ^ 2 := pow_le_pow_left₀ hp0 hp2 2
    have : ((p ^ 2 + p + 1 : ℕ) : ℝ) ≤ N := by
      push_cast
      nlinarith
    exact_mod_cast this
  have := (singer_construction p hp.isPrimePow).trans (h_mono hpN)
  have hcast : ((p + 1 : ℕ) : ℝ) ≤ (h N : ℝ) := by exact_mod_cast this
  push_cast at hcast
  have : a * s = (1 - ε) * s := rfl
  linarith

end SGAux

end

open Filter in
theorem solution :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (1 - ε) * Real.sqrt N ≤ (Erdos30.h N : ℝ) :=
  SGAux.main
