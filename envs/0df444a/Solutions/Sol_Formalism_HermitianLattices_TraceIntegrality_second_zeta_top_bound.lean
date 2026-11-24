-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.second_zeta_top_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:11:23.609775+00:00
-- url     : https://prove2.me/submissions/79b3845e-d92f-494c-b85f-22bcdbde812d

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
private lemma stirling_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  have h := Stirling.le_log_factorial_stirling (n := n) (by omega)
  have h1 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have h2 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith
private lemma stirling_upper_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + Real.log n + 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    have key : Real.log ((n : ℝ) / (n + 1)) ≤ (n : ℝ) / (n + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at key
    have e : (n : ℝ) / (n + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by field_simp; ring
    rw [e] at key
    have k2 : ((n : ℝ) + 1) * (Real.log n - Real.log ((n : ℝ) + 1)) ≤ -1 := by
      have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
      have e2 : ((n : ℝ) + 1) * -(1 / ((n : ℝ) + 1)) = -1 := by field_simp
      linarith
    nlinarith
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
private lemma log_factorial_shift_bound (n k : ℕ) (x : ℝ) (h : ((n + k : ℕ) : ℝ) ≤ x) :
    Real.log ((n + k).factorial : ℝ) ≤ Real.log (n.factorial : ℝ) + k * Real.log x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h' : ((n + k : ℕ) : ℝ) ≤ x := by push_cast at h ⊢; linarith
    have h1 := ih h'
    rw [← add_assoc, Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    have h2 : Real.log ((n : ℝ) + k + 1) ≤ Real.log x :=
      Real.log_le_log (by positivity) (by push_cast at h; linarith)
    nlinarith
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
set_option maxHeartbeats 800000
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : LargestPlaceHookBound := by
  intro C₀ hC
  refine ⟨21 + (3 + C₀) ^ 2 + C₀ * (2 + C₀), ?_⟩
  intro R nu A w a b' L logOm hnu h0 hw hrow haA hA2 hb1 hba hL hla hRb hOm
  have ha1 : (1 : ℝ) ≤ a := hb1.trans hba
  have hA1r : (1 : ℝ) ≤ A := ha1.trans haA
  have hA1 : 1 ≤ A := by exact_mod_cast hA1r
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  set l5 := Real.log (5 * a) with hl5def
  have hl5 : l5 ≤ 5 * L := by
    rw [hl5def, Real.log_mul (by norm_num) (by linarith)]
    have : Real.log 5 ≤ 5 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hl50 : 0 ≤ l5 := Real.log_nonneg (by linarith)
  set X := (3 + C₀) * b' with hX
  have hX1 : 1 ≤ X := by nlinarith
  have hlX : Real.log X ≤ (3 + C₀) * L := by
    rw [hX, Real.log_mul (by linarith) (by linarith)]
    have h1 : Real.log (3 + C₀) ≤ (3 + C₀) - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have h2 : Real.log b' ≤ Real.log a := Real.log_le_log (by linarith) hba
    nlinarith
  have hlX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  obtain ⟨hup, hlo⟩ := log_hook_product_bounds R nu hnu
  rw [Fin.sum_univ_succ] at hup hlo
  have e0 : nu 0 + R - ((0 : Fin (R + 1)) : ℕ) = A + (w + R) := by
    have : ((0 : Fin (R + 1)) : ℕ) = 0 := rfl
    omega
  rw [e0] at hup hlo
  obtain ⟨hT0, hTU⟩ := sum_log_factorial_rows_bounds R (fun i : Fin R => nu i.succ + R - (i.succ : Fin (R + 1))) X hX1 (by
    intro i
    have h1 : ((nu i.succ + R - (i.succ : Fin (R + 1)) : ℕ) : ℝ) ≤ ((nu i.succ + R : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.sub_le _ _)
    have h2 := hrow i.succ (Fin.succ_ne_zero i)
    push_cast at h1
    rw [hX]
    linarith)
  set Tl := ∑ i : Fin R, Real.log ((nu i.succ + R - (i.succ : Fin (R + 1)) : ℕ).factorial : ℝ) with hTl
  obtain ⟨hS0, hSU⟩ := sum_rows_bounds R (fun i : Fin R => nu i.succ) ((2 + C₀) * b')
    (fun i => hrow i.succ (Fin.succ_ne_zero i))
  have hsum : ∑ i, (nu i : ℝ) = (A : ℝ) + w + ∑ i : Fin R, (nu i.succ : ℝ) := by
    rw [Fin.sum_univ_succ, h0]; push_cast; ring
  set S := ∑ i : Fin R, (nu i.succ : ℝ) with hS
  have hsh := log_factorial_shift_bound A (w + R) (5 * a) (by push_cast; linarith)
  have hmono : Real.log (A.factorial : ℝ) ≤ Real.log ((A + (w + R)).factorial : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.factorial_le (Nat.le_add_right _ _))
  have hlo' := stirling_lower_bound A hA1
  have hhi' := stirling_upper_bound A hA1
  have hlA : Real.log (A : ℝ) ≤ l5 := Real.log_le_log (by linarith) (by linarith)
  have hl0 : Real.log ((nu 0 : ℝ) + R + 1) ≤ l5 := by
    apply Real.log_le_log (by positivity)
    rw [h0]; push_cast; linarith
  set Q := ((R : ℝ) + 1) * b' * L with hQ
  have hbL : b' * L ≤ Q := by
    have := mul_nonneg hR0 (mul_nonneg (by linarith : (0:ℝ) ≤ b') (by linarith : (0:ℝ) ≤ L))
    rw [hQ]; linarith
  have hLQ : L ≤ Q := (le_mul_of_one_le_left (by linarith) hb1).trans hbL
  have t1 : ((w + R : ℕ) : ℝ) * l5 ≤ 15 * Q := by
    have : ((w + R : ℕ) : ℝ) ≤ 3 * b' := by push_cast; linarith
    calc ((w + R : ℕ) : ℝ) * l5 ≤ (3 * b') * (5 * L) := mul_le_mul this hl5 hl50 (by linarith)
      _ = 15 * (b' * L) := by ring
      _ ≤ 15 * Q := by linarith
  have t2 : (R : ℝ) * (X * Real.log X) ≤ (3 + C₀) ^ 2 * Q := by
    have h1 : X * Real.log X ≤ X * ((3 + C₀) * L) := mul_le_mul_of_nonneg_left hlX (by linarith)
    have h2 : (R : ℝ) * (X * Real.log X) ≤ ((R : ℝ) + 1) * (X * ((3 + C₀) * L)) :=
      mul_le_mul (by linarith) h1 (mul_nonneg (by linarith) hlX0) (by linarith)
    calc _ ≤ _ := h2
      _ = (3 + C₀) ^ 2 * Q := by rw [hX, hQ]; ring
  have t3 : ((R : ℝ) + 1) ^ 2 * Real.log ((nu 0 : ℝ) + R + 1) ≤ 5 * Q := by
    have h1 : ((R : ℝ) + 1) ^ 2 ≤ ((R : ℝ) + 1) * b' := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hRb (by linarith)
    calc _ ≤ ((R : ℝ) + 1) ^ 2 * l5 := mul_le_mul_of_nonneg_left hl0 (by positivity)
      _ ≤ (((R : ℝ) + 1) * b') * (5 * L) := mul_le_mul h1 hl5 hl50 (mul_nonneg (by linarith) (by linarith))
      _ = 5 * Q := by rw [hQ]; ring
  have t4 : |((w : ℝ) + S) * logOm| ≤ C₀ * (2 + C₀) * Q := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (w : ℝ) + S)]
    have h1 : (w : ℝ) + S ≤ ((R : ℝ) + 1) * ((2 + C₀) * b') := by
      have := mul_nonneg hC (by linarith : (0:ℝ) ≤ b')
      linarith
    calc ((w : ℝ) + S) * |logOm| ≤ (((R : ℝ) + 1) * ((2 + C₀) * b')) * (C₀ * L) :=
          mul_le_mul h1 hOm (abs_nonneg _)
            (mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith)))
      _ = C₀ * (2 + C₀) * Q := by rw [hQ]; ring
  have hgoal : placeTerm nu logOm - topTerm A logOm
      = (Real.log (hookF nu) - ((A : ℝ) * Real.log A - A)) - ((w : ℝ) + S) * logOm := by
    unfold placeTerm topTerm; rw [hsum]; ring
  have hfin : (21 + (3 + C₀) ^ 2 + C₀ * (2 + C₀)) * ((R : ℝ) + 1) * b' * L
      = (21 + (3 + C₀) ^ 2 + C₀ * (2 + C₀)) * Q := by rw [hQ]; ring
  rw [hgoal, hfin]
  obtain ⟨t4a, t4b⟩ := abs_le.mp t4
  have hQ0 : 0 ≤ Q := by linarith
  have hsq : 0 ≤ (3 + C₀) ^ 2 * Q := by positivity
  rw [abs_le]
  constructor <;> linarith
end Formalism.HermitianLattices.TraceIntegrality
