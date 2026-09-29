-- Prove2me | solution 1 for ChebyshevBounds.primes_in_interval_ge
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T12:18:58.464269+00:00
-- url     : https://prove2.me/submissions/27d0d94b-d43f-428c-91dd-e2d57de41270

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Maynard.ChebyshevInterval =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Maynard track, node N3.5: Chebyshev interval prime-supply bound

Target: `π(64N) − π(N) ≥ c·N / log N` for an explicit positive constant `c`
and an explicit threshold `N₀`, where `π = Nat.primeCounting`.

Route (per the N2.0 review): combine mathlib's Chebyshev bounds
`Chebyshev.pi_ge` (a lower bound `(n log 2 − log(n+1))/log n ≤ π n`) and
`Chebyshev.pi_le_log4_mul_div` (an explicit upper bound
`π ⌊x⌋₊ ≤ log 4 · x / log √x + √x`). Applying the first at `64N` and the
second at `N`, the leading term is `(64 log 2)·N/log(64N) − (log 4)·N/log √N`.
Since `log(64N) ≤ 2 log N` (for `N ≥ 64`) and `log √N = (log N)/2`, this is
`≥ (32 log 2 − 4 log 2)·N/log N = 28 log 2 · N/log N`, and the lower-order
terms `log(64N+1)` and `√N` are `o(N/log N)`, absorbed with margin. The
conspiracy barrier is at `K₀ = 2`; `K₀ = 64` clears it comfortably, so
`c = 1` works with room to spare.
-/

open Filter Asymptotics Real Topology
open scoped Nat.Prime

namespace Salt.Maynard

/-- `log N / √N → 0`: the source of the `√N` lower-order term being
negligible against `N/log N`. -/
private theorem tendsto_logNat_div_sqrt :
    Tendsto (fun N : ℕ => Real.log N / Real.sqrt N) atTop (𝓝 0) := by
  have h : (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) =
      (fun x : ℝ => Real.log x / Real.sqrt x) := by
    funext x; rw [Real.sqrt_eq_rpow]
  have hlo : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1 / 2)).tendsto_div_nhds_zero
  rw [h] at hlo
  exact hlo.comp tendsto_natCast_atTop_atTop

/-- `log(64N+1) / N → 0`: the `log(64N+1)` numerator term in the `π(64N)`
lower bound is negligible against `N`. -/
private theorem tendsto_logNat_succ_div :
    Tendsto (fun N : ℕ => Real.log (64 * N + 1) / N) atTop (𝓝 0) := by
  -- `log x / x → 0`, composed with `x = 64N+1 → ∞`, times `(64N+1)/N → 64`.
  have h1 : Tendsto (fun N : ℕ => Real.log (64 * (N:ℝ) + 1) / (64 * (N:ℝ) + 1))
      atTop (𝓝 0) := by
    have hlo : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hg : Tendsto (fun N : ℕ => 64 * (N:ℝ) + 1) atTop atTop := by
      apply Filter.tendsto_atTop_add_const_right
      exact (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 64))
    exact hlo.comp hg
  have h2 : Tendsto (fun N : ℕ => (64 * (N:ℝ) + 1) / (N:ℝ)) atTop (𝓝 64) := by
    have : (fun N : ℕ => (64 * (N:ℝ) + 1) / (N:ℝ))
        =ᶠ[atTop] (fun N : ℕ => 64 + 1 / (N:ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hN0 : (N:ℝ) ≠ 0 := by positivity
      field_simp
    rw [tendsto_congr' this]
    have : Tendsto (fun N : ℕ => 1 / (N:ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds.add this)
  have := h1.mul h2
  simp only [zero_mul] at this
  refine (tendsto_congr' ?_).mp this
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hb : 64 * (N:ℝ) + 1 ≠ 0 := by positivity
  have hn : (N:ℝ) ≠ 0 := by positivity
  field_simp

/-- **N3.5**: the prime-supply lower bound. For `K₀ = 64` and all `N ≥ N₀`,
`π(64N) − π(N) ≥ c·N/log N` with an explicit positive constant `c = 1`.
Here `π = Nat.primeCounting`. Loose but sufficient for the Maynard sieve. -/
theorem primes_in_interval_ge :
    ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧ ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) / Real.log N ≤
        ((Nat.primeCounting (64 * N) : ℝ) - (Nat.primeCounting N : ℝ)) := by
  have key : ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) * (N : ℝ) / Real.log N ≤
        ((Nat.primeCounting (64 * N) : ℝ) - (Nat.primeCounting N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 64,
        tendsto_logNat_div_sqrt.eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
        tendsto_logNat_succ_div.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)]
      with N hN64 hsqrt hsucc
    -- Basic positivity facts.
    have hN1 : (1 : ℝ) < (N : ℝ) := by
      have : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN64
      linarith
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    set L := Real.log (N : ℝ) with hLdef
    have hL : 0 < L := Real.log_pos hN1
    set s := Real.sqrt (N : ℝ) with hsdef
    have hs0 : 0 < s := Real.sqrt_pos.mpr hN0
    have hss : s * s = (N : ℝ) := Real.mul_self_sqrt hN0.le
    have hlogs : Real.log s = L / 2 := by
      rw [hsdef, Real.log_sqrt hN0.le, hLdef]
    -- `L < s` from `log N / √N < 1`.
    have hLs : L < s := by
      have h := hsqrt; rw [div_lt_one hs0] at h; exact h
    have hsL : s * L ≤ (N : ℝ) := by nlinarith [hLs, hs0, hL]
    -- `log(64N+1) < N` from `log(64N+1)/N < 1`.
    have hsucc' : Real.log (64 * (N : ℝ) + 1) < (N : ℝ) := by
      have h := hsucc; rw [div_lt_one hN0] at h; exact h
    have h64N1 : (1 : ℝ) < 64 * (N : ℝ) := by nlinarith
    have hD : 0 < Real.log (64 * (N : ℝ)) := Real.log_pos h64N1
    have hD2 : Real.log (64 * (N : ℝ)) ≤ 2 * L := by
      rw [Real.log_mul (by norm_num) (by positivity), hLdef]
      have hlog64 : Real.log 64 ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hN64)
      linarith
    -- Numeric constant: `log 2 > 0.693…`.
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    -- Lower bound on `π(64N)` (Chebyshev), cleared of the denominator.
    have hpi64 := Chebyshev.pi_ge (64 * N)
    push_cast at hpi64
    rw [div_le_iff₀ hD] at hpi64
    -- hpi64 : 64*N*log2 - log(64*N+1) ≤ π(64N) * log(64N)
    have hc64 : (0 : ℝ) ≤ (Nat.primeCounting (64 * N) : ℝ) := by positivity
    have hπ64L : 64 * (N : ℝ) * Real.log 2 - Real.log (64 * (N : ℝ) + 1)
        ≤ (Nat.primeCounting (64 * N) : ℝ) * (2 * L) :=
      hpi64.trans (mul_le_mul_of_nonneg_left hD2 hc64)
    -- Upper bound on `π(N)` (Chebyshev), cleared of the denominator.
    have hpiN := Chebyshev.pi_le_log4_mul_div hN1
    rw [Nat.floor_natCast, hlogs] at hpiN
    -- hpiN : ↑(π N) ≤ log4 * N / (L/2) + s
    have hLne : L ≠ 0 := ne_of_gt hL
    have haux : Real.log 4 * (N : ℝ) / (L / 2) * L = 2 * Real.log 4 * (N : ℝ) := by
      field_simp
    have hpiN' : (Nat.primeCounting N : ℝ) * L
        ≤ 2 * Real.log 4 * (N : ℝ) + s * L := by
      have h := mul_le_mul_of_nonneg_right hpiN hL.le
      rw [add_mul, haux] at h
      linarith
    -- Assemble.
    rw [one_mul, div_le_iff₀ hL]
    nlinarith [hπ64L, hpiN', hlog2, hlog4, hsL, hsucc', hN0, hL,
      mul_le_mul_of_nonneg_right hlog2.le hN0.le]
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp key
  exact ⟨1, N₀, one_pos, hN₀⟩

end Salt.Maynard

end




theorem solution :
    ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧ ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) / Real.log N ≤
        ((Nat.primeCounting (64 * N) : ℝ) - (Nat.primeCounting N : ℝ)) :=
  Salt.Maynard.primes_in_interval_ge

