-- Prove2me | solution 1 for Erdos679.additive_refutation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:06:02.725942+00:00
-- url     : https://prove2.me/submissions/6e03596f-e02c-43d3-9430-dfe86f061865

module
public import Definitions.Def_Erdos679_Analytic
public import Definitions.Def_Erdos679_Gap
public import Definitions.Def_Erdos679_CRT
public import Definitions.Def_Erdos679AdditiveRefutation_Solution
public import Theorems.Thm_Erdos679_eventually_shifted_log_primeProduct_le
public import Theorems.Thm_Erdos679_eventually_shifted_log_primeProduct_gt
public import Theorems.Thm_Erdos679_cardDistinctFactors_primeProduct
public import Theorems.Thm_Erdos679_eventually_finite_window_lifting
public import Theorems.Thm_Erdos679_gap_from_log_bounds
public import Theorems.Thm_Erdos679_log_log_quotient_mono
public import Theorems.Thm_Erdos679_primeProduct_pos


set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution (C : ℝ) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ k < n, K < k ∧
      log (k : ℝ) / log (log k) + C ≤
        (ArithmeticFunction.cardDistinctFactors (n - k) : ℝ) := by
  let K₀ := max K (Nat.ceil (exp (exp 1)) + 1)
  have hK : K ≤ K₀ := le_max_left _ _
  have hKlarge : exp (exp 1) < (K₀ : ℝ) := by
    have hceil : exp (exp 1) ≤ (Nat.ceil (exp (exp 1)) : ℝ) := Nat.le_ceil _
    have hlt : (Nat.ceil (exp (exp 1)) : ℝ) < (K₀ : ℝ) := by
      exact_mod_cast (Nat.lt_succ_self (Nat.ceil (exp (exp 1)))).trans_le (le_max_right K _)
    exact hceil.trans_lt hlt
  let θ : ℕ → ℝ := fun m => log ((primeProduct m + K₀ : ℕ) : ℝ)
  have hgap := gap_from_log_bounds θ (1 / 5) (by norm_num)
    (eventually_shifted_log_primeProduct_le K₀)
    (eventually_shifted_log_primeProduct_gt K₀) C
  obtain ⟨m, hm⟩ := hgap.exists
  have hwindow : ∀ k, K₀ < k → k ≤ K₀ + primeProduct m →
      log (k : ℝ) / log (log k) + C ≤
        (ArithmeticFunction.cardDistinctFactors (primeProduct m) : ℝ) := by
    intro k hklo hkhi
    have hk : exp (exp 1) < (k : ℝ) :=
      hKlarge.trans (Nat.cast_lt.mpr hklo)
    have hxy : (k : ℝ) ≤ ((K₀ + primeProduct m : ℕ) : ℝ) := Nat.cast_le.mpr hkhi
    have hmono := log_log_quotient_mono hk hxy
    have hbound : log ((K₀ + primeProduct m : ℕ) : ℝ) /
        log (log ((K₀ + primeProduct m : ℕ) : ℝ)) + C < (m : ℝ) := by
      simpa only [θ, Nat.add_comm] using hm
    rw [cardDistinctFactors_primeProduct]
    linarith
  have hlift := eventually_finite_window_lifting (primeProduct m) K₀
    (primeProduct_pos m) (fun k => log (k : ℝ) / log (log k)) C hwindow
  filter_upwards [hlift] with n hn
  obtain ⟨k, hkn, hklo, hbound⟩ := hn
  exact ⟨k, hkn, hK.trans_lt hklo, hbound⟩
end Erdos679
