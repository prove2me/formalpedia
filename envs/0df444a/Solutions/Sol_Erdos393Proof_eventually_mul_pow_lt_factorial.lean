-- Prove2me | solution 1 for Erdos393Proof.eventually_mul_pow_lt_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:32:11.169805+00:00
-- url     : https://prove2.me/submissions/cac3a2c0-3e3e-4830-939a-5aeec1ca9fe4

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393Proof
open ABC Polynomial
namespace Erdos393Proof
theorem _root_.solution (K X : ℕ) : ∀ᶠ n in atTop, K * X ^ n < n ! := by
  have h2 : ∀ᶠ n in atTop, (X : ℝ) ^ n / n ! < 1 / (K + 1) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (X : ℝ)).eventually (gt_mem_nhds (by positivity))
  filter_upwards [h2] with n hn
  have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [div_lt_div_iff₀ hf (by positivity), one_mul] at hn
  have hX : (0 : ℝ) ≤ (X : ℝ) ^ n := by positivity
  have : (K : ℝ) * X ^ n < n ! := by nlinarith
  exact_mod_cast this
end Erdos393Proof
