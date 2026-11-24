-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.second_zeta_thin_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:10:36.15187+00:00
-- url     : https://prove2.me/submissions/f4ecccb8-8536-4b6d-b8ff-60c3bf07e152

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumLogFactorialRowsBounds
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_hook_den_bounds
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_hook_product_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
private lemma log_factorial_row_bound (n : ℕ) (x : ℝ) (hx : 1 ≤ x) (h : (n : ℝ) ≤ x) :
    Real.log (n.factorial : ℝ) ≤ x * Real.log x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using mul_nonneg (by linarith) (Real.log_nonneg hx)
  have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have h2 : Real.log (n : ℝ) ≤ Real.log x := Real.log_le_log (by exact_mod_cast hn) h
  have h3 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  calc Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log (by positivity) h1
    _ = n * Real.log n := Real.log_pow _ _
    _ ≤ x * Real.log x := mul_le_mul h h2 h3 (by linarith)
private lemma sum_log_factorial_rows_bounds (k : ℕ) (g : Fin k → ℕ) (x : ℝ) (hx : 1 ≤ x) (h : ∀ i, (g i : ℝ) ≤ x) :
    0 ≤ ∑ i, Real.log ((g i).factorial : ℝ) ∧
      ∑ i, Real.log ((g i).factorial : ℝ) ≤ k * (x * Real.log x) := by
  constructor
  · exact Finset.sum_nonneg fun i _ => Real.log_nonneg (by exact_mod_cast Nat.factorial_pos _)
  · calc ∑ i, Real.log ((g i).factorial : ℝ) ≤ ∑ _i : Fin k, x * Real.log x :=
          Finset.sum_le_sum fun i _ => log_factorial_row_bound _ _ hx (h i)
      _ = k * (x * Real.log x) := by simp
private lemma log_hook_product_bounds (R : ℕ) (nu : Fin (R + 1) → ℕ) (h : Antitone nu) :
    Real.log (hookF nu) ≤ ∑ i : Fin (R + 1), Real.log ((nu i + R - i : ℕ).factorial : ℝ) ∧
    ∑ i : Fin (R + 1), Real.log ((nu i + R - i : ℕ).factorial : ℝ)
        - ((R : ℝ) + 1) ^ 2 * Real.log ((nu 0 : ℝ) + R + 1) ≤ Real.log (hookF nu) := by
  obtain ⟨h1, h2, -⟩ := Formalism.LogVandermondeBounds.flipTwoThree.hook_product_bounds R nu h
  refine ⟨?_, h2⟩
  have hpos : 0 < hookF nu := by
    unfold Formalism.LogVandermondeBounds.flipTwoThree.hookF
    apply div_pos (by positivity)
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    linarith [(Formalism.LogVandermondeBounds.flipTwoThree.hook_den_bounds R nu h i j (mem_filter.mp hj).2).1]
  calc Real.log (hookF nu) ≤ Real.log (∏ i : Fin (R + 1), ((nu i + R - i : ℕ).factorial : ℝ)) :=
        Real.log_le_log hpos h1
    _ = _ := Real.log_prod (fun i _ => by positivity)
private lemma sum_rows_bounds (k : ℕ) (g : Fin k → ℕ) (x : ℝ) (h : ∀ i, (g i : ℝ) ≤ x) :
    0 ≤ ∑ i, (g i : ℝ) ∧ ∑ i, (g i : ℝ) ≤ k * x := by
  constructor
  · exact Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  · calc ∑ i, (g i : ℝ) ≤ ∑ _i : Fin k, x := Finset.sum_le_sum fun i _ => h i
      _ = k * x := by simp
end Formalism.HermitianLattices.TraceIntegrality
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : ThinPlaceHookBound := by
  intro C₀ hC
  refine ⟨(3 + C₀) ^ 2 + C₀ * (2 + C₀), ?_⟩
  intro R nu b' L logOm hnu hrow hb1 hL hlb hRb hOm
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  set X := (3 + C₀) * b' with hX
  have hX1 : 1 ≤ X := by nlinarith
  have hlX : Real.log X ≤ (3 + C₀) * L := by
    rw [hX, Real.log_mul (by linarith) (by linarith)]
    have h1 : Real.log (3 + C₀) ≤ (3 + C₀) - 1 := Real.log_le_sub_one_of_pos (by linarith)
    nlinarith
  have hlX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  obtain ⟨hup, hlo⟩ := log_hook_product_bounds R nu hnu
  obtain ⟨hT0, hTU⟩ := sum_log_factorial_rows_bounds (R + 1) (fun i : Fin (R + 1) => nu i + R - (i : ℕ)) X hX1 (by
    intro i
    have h1 : ((nu i + R - (i : ℕ) : ℕ) : ℝ) ≤ ((nu i + R : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.sub_le _ _)
    have h2 := hrow i
    push_cast at h1
    rw [hX]
    linarith)
  set Tl := ∑ i : Fin (R + 1), Real.log ((nu i + R - (i : ℕ) : ℕ).factorial : ℝ) with hTl
  obtain ⟨hS0, hSU⟩ := sum_rows_bounds (R + 1) nu ((2 + C₀) * b') hrow
  set S := ∑ i, (nu i : ℝ) with hS
  have hl0 : Real.log ((nu 0 : ℝ) + R + 1) ≤ Real.log X := by
    apply Real.log_le_log (by positivity)
    have := hrow 0
    rw [hX]; linarith
  set Q := ((R : ℝ) + 1) * b' * L with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have t2 : ((R + 1 : ℕ) : ℝ) * (X * Real.log X) ≤ (3 + C₀) ^ 2 * Q := by
    have h1 : X * Real.log X ≤ X * ((3 + C₀) * L) := mul_le_mul_of_nonneg_left hlX (by linarith)
    calc ((R + 1 : ℕ) : ℝ) * (X * Real.log X) ≤ ((R + 1 : ℕ) : ℝ) * (X * ((3 + C₀) * L)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = (3 + C₀) ^ 2 * Q := by rw [hX, hQ]; push_cast; ring
  have t3 : ((R : ℝ) + 1) ^ 2 * Real.log ((nu 0 : ℝ) + R + 1) ≤ (3 + C₀) * Q := by
    have h1 : ((R : ℝ) + 1) ^ 2 ≤ ((R : ℝ) + 1) * b' := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hRb (by linarith)
    calc _ ≤ ((R : ℝ) + 1) ^ 2 * Real.log X := mul_le_mul_of_nonneg_left hl0 (by positivity)
      _ ≤ (((R : ℝ) + 1) * b') * ((3 + C₀) * L) := mul_le_mul h1 hlX hlX0 (mul_nonneg (by linarith) (by linarith))
      _ = (3 + C₀) * Q := by rw [hQ]; ring
  have t4 : |S * logOm| ≤ C₀ * (2 + C₀) * Q := by
    rw [abs_mul, abs_of_nonneg hS0]
    calc S * |logOm| ≤ (((R + 1 : ℕ) : ℝ) * ((2 + C₀) * b')) * (C₀ * L) :=
          mul_le_mul hSU hOm (abs_nonneg _) (by positivity)
      _ = C₀ * (2 + C₀) * Q := by rw [hQ]; push_cast; ring
  have hfin : ((3 + C₀) ^ 2 + C₀ * (2 + C₀)) * ((R : ℝ) + 1) * b' * L
      = ((3 + C₀) ^ 2 + C₀ * (2 + C₀)) * Q := by rw [hQ]; ring
  unfold placeTerm
  rw [hfin]
  obtain ⟨t4a, t4b⟩ := abs_le.mp t4
  have h33 : (3 + C₀) * Q ≤ (3 + C₀) ^ 2 * Q := by
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 3 + C₀) (by linarith : (0:ℝ) ≤ 2 + C₀)) hQ0
    linarith
  rw [abs_le]
  constructor <;> linarith
end Formalism.HermitianLattices.TraceIntegrality
