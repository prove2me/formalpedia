-- Prove2me | solution 1 for Freiman.continuant_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T19:45:36.500729+00:00
-- url     : https://prove2.me/submissions/d653ee42-d50a-4cfa-b195-f2402c10cd6b

import Definitions.Def_Freiman_perronArithmetic
import Theorems.Thm_Freiman_cf_convergence
import Theorems.Thm_Freiman_cfValue_prefix
import Theorems.Thm_Freiman_prefixEval_mobius
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_continuant_determinant
import Theorems.Thm_Freiman_continuant_append
import Mathlib.Tactic.FieldSimp

open Freiman

set_option autoImplicit false

private theorem error_algebra (p pp q qp τ x : ℝ)
    (hq : 0 < q) (hqp : 0 ≤ qp) (hτ : 0 < τ)
    (hx : x = (p + τ * pp) / (q + τ * qp))
    (hdet : |pp * q - p * qp| = 1) :
    |q * x - p| = τ / (q + τ * qp) := by
  have hd : 0 < q + τ * qp := by positivity
  have heq : q * x - p = τ * (pp * q - p * qp) / (q + τ * qp) := by
    rw [hx]
    field_simp
    <;> ring
  rw [heq, abs_div, abs_mul, abs_of_pos hτ, hdet, abs_of_pos hd, mul_one]

theorem solution (b : ℕ → ℕ+) (n : ℕ) :
    |(continuantQ b n : ℝ) * cfValue b - (continuantP b n : ℝ)| <
      1 / (continuantQ b (n + 1) : ℝ) := by
  let w := (List.range n).map b
  let τ := cfValue (fun k => b (n + k))
  let σ := cfValue (fun k => b (n + (k + 1)))
  have hτ : 0 < τ := (cf_convergence _).2.2.1
  have hσ : 0 < σ := (cf_convergence _).2.2.1
  have hq : 0 < (wordContinuantQ w : ℝ) := by
    exact_mod_cast continuant_denominator_pos w
  have hqp : 0 ≤ (wordContinuantPrevQ w : ℝ) := Nat.cast_nonneg _
  have htail : τ = 1 / (((b n : ℕ) : ℝ) + σ) := by
    simpa [τ, σ] using (cf_convergence (fun k => b (n + k))).2.2.2.2
  have hrel : τ * (((b n : ℕ) : ℝ) + σ) = 1 := by
    rw [htail]
    have ha : 0 < ((b n : ℕ) : ℝ) := by exact_mod_cast (b n).pos
    field_simp
  have hdet : |(wordContinuantPrevP w : ℝ) * wordContinuantQ w -
      (wordContinuantP w : ℝ) * wordContinuantPrevQ w| = 1 := by
    have hi := continuant_determinant w
    have hr : (wordContinuantPrevP w : ℝ) * wordContinuantQ w -
        (wordContinuantP w : ℝ) * wordContinuantPrevQ w = (-1 : ℝ) ^ w.length := by
      exact_mod_cast hi
    rw [hr, abs_pow]
    norm_num
  have hx : cfValue b =
      ((wordContinuantP w : ℝ) + τ * wordContinuantPrevP w) /
      ((wordContinuantQ w : ℝ) + τ * wordContinuantPrevQ w) := by
    rw [cfValue_prefix b n]
    exact prefixEval_mobius w τ hτ.le
  have herr := error_algebra _ _ _ _ _ _ hq hqp hτ hx hdet
  have hnext : (continuantQ b (n + 1) : ℝ) =
      ((b n : ℕ) : ℝ) * wordContinuantQ w + wordContinuantPrevQ w := by
    simp only [continuantQ, List.range_succ, List.map_append, List.map_singleton]
    change ((wordContinuantData (w ++ [b n])).2.2 : ℝ) = _
    rw [continuant_append]
    push_cast
    rfl
  change |(wordContinuantQ w : ℝ) * cfValue b - (wordContinuantP w : ℝ)| < _
  rw [herr, hnext]
  have hd : 0 < (wordContinuantQ w : ℝ) + τ * wordContinuantPrevQ w := by positivity
  have hn : 0 < ((b n : ℕ) : ℝ) * wordContinuantQ w + wordContinuantPrevQ w := by
    have ha : 0 < ((b n : ℕ) : ℝ) := by exact_mod_cast (b n).pos
    positivity
  apply (div_lt_div_iff₀ hd hn).2
  have hp := mul_pos (mul_pos hτ hσ) hq
  nlinarith [congrArg (fun y : ℝ => y * (wordContinuantQ w : ℝ)) hrel]
