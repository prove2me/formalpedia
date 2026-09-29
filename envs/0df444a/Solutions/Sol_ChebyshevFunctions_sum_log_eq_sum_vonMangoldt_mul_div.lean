-- Prove2me | solution 1 for ChebyshevFunctions.sum_log_eq_sum_vonMangoldt_mul_div
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T18:09:50.346968+00:00
-- url     : https://prove2.me/submissions/e141634d-a36b-4891-a6de-2c948901a203

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Maynard.Mertens =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# N3.2 — Mertens' second theorem, upper bound

`Σ_{p ≤ x} 1/p ≤ log log x + C`.  mathlib has no Mertens theorems, so this
is built from the von Mangoldt convolution + Chebyshev's `ψ`-bound + Abel
summation.  Only the UPPER direction is needed downstream (N3.4 → N5.2).

Route (see the node brief):
* **Step 1** `Σ_{n≤N} log n ≤ N log N`.
* **Step 2** divisor swap `Σ_{n≤N} log n = Σ_{d≤N} Λ d · ⌊N/d⌋`.
* **Step 3/4** ⇒ `Σ_{p≤N} (log p)/p ≤ log N + c`  (Mertens' 1st, upper).
* **Step 5** Abel summation against the weight `1/log t` ⇒ the log-log bound.
-/

open Finset ArithmeticFunction

namespace Salt.Maynard

/-! ## Step 2 — the divisor swap -/

/-- For `0 < n ≤ N`, the divisors of `n` are exactly the elements of
`Ioc 0 N` dividing `n`. -/
theorem divisors_eq_filter_Ioc {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    n.divisors = (Finset.Ioc 0 N).filter (· ∣ n) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hd, _⟩
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
    have hdn : d ≤ n := Nat.le_of_dvd hn hd
    exact ⟨⟨hdpos, hdn.trans hnN⟩, hd⟩
  · rintro ⟨⟨_, _⟩, hd⟩
    exact ⟨hd, hn.ne'⟩

/-- **Step 2.** `Σ_{n=1}^{N} log n = Σ_{d=1}^{N} Λ d · ⌊N/d⌋`. -/
theorem sum_log_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n
      = ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  -- rewrite each `log n` as `Σ_{d ∣ n} Λ d`, extended over `Ioc 0 N`
  have hstep : ∑ n ∈ Finset.Ioc 0 N, Real.log n
      = ∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ Finset.Ioc 0 N,
          (if d ∣ n then Λ d else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [← ArithmeticFunction.vonMangoldt_sum (n := n),
      divisors_eq_filter_Ioc hn.1 hn.2, Finset.sum_filter]
  rw [hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  -- `Σ_n (if d ∣ n then Λ d else 0) = Λ d · #{n ∈ Ioc 0 N : d ∣ n} = Λ d · (N/d)`
  rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div,
    nsmul_eq_mul, mul_comm]

/-! ## Step 1 — the log-sum upper bound -/

/-- **Step 1.** `Σ_{n=1}^{N} log n ≤ N · log N`. -/
theorem sum_log_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n ≤ (N : ℝ) * Real.log N := by
  have hle : ∑ n ∈ Finset.Ioc 0 N, Real.log n
      ≤ ∑ _n ∈ Finset.Ioc 0 N, Real.log N := by
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ioc] at hn
    apply Real.log_le_log (by exact_mod_cast hn.1)
    exact_mod_cast hn.2
  rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul] at hle
  exact hle

/-! ## Steps 3 & 4 — Mertens' first theorem, upper bound -/

/-- `⌊N/d⌋ ≥ N/d − 1` as reals, for `0 < d`. -/
theorem cast_div_ge {N d : ℕ} (hd : 0 < d) :
    (N : ℝ) / d - 1 ≤ ((N / d : ℕ) : ℝ) := by
  have hdm := Nat.div_add_mod N d
  have hlt := Nat.mod_lt N hd
  have hnat : N ≤ d * (N / d) + d := by omega
  have hcast : (N : ℝ) ≤ (d : ℝ) * ((N / d : ℕ) : ℝ) + d := by exact_mod_cast hnat
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [sub_le_iff_le_add]
  rw [div_le_iff₀ hdr]
  nlinarith [hcast]

/-- `Σ_{d≤N} Λ d = ψ N`, packaged at a `Nat` argument. -/
theorem sum_vonMangoldt_eq_psi (N : ℕ) :
    ∑ d ∈ Finset.Ioc 0 N, Λ d = Chebyshev.psi (N : ℝ) := by
  rw [Chebyshev.psi, Nat.floor_natCast]

/-- **Steps 3 & 4.** `Σ_{d≤N} Λ d / d ≤ log N + (log 4 + 4)`, for `1 ≤ N`. -/
theorem sum_vonMangoldt_div_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Ioc 0 N, Λ d / d ≤ Real.log N + (Real.log 4 + 4) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- lower bound on the divisor-swap sum
  have hlow : (N : ℝ) * (∑ d ∈ Finset.Ioc 0 N, Λ d / d)
        - (∑ d ∈ Finset.Ioc 0 N, Λ d)
      ≤ ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
    have hge : (N : ℝ) / d - 1 ≤ ((N / d : ℕ) : ℝ) := cast_div_ge hd.1
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd.1
    have : (N : ℝ) * (Λ d / d) - Λ d = Λ d * ((N : ℝ) / d - 1) := by
      have hdne : (d : ℝ) ≠ 0 := hdr.ne'
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hge hΛ
  -- upper bounds: Step 1 and Chebyshev's ψ-bound
  have hstep1 : ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N := by
    rw [← sum_log_eq_sum_vonMangoldt_mul_div]
    exact sum_log_le N
  have hpsi : ∑ d ∈ Finset.Ioc 0 N, Λ d ≤ (Real.log 4 + 4) * N := by
    rw [sum_vonMangoldt_eq_psi]
    exact Chebyshev.psi_le_const_mul_self hNr.le
  -- combine and divide by N
  have hcomb : (N : ℝ) * (∑ d ∈ Finset.Ioc 0 N, Λ d / d)
      ≤ (N : ℝ) * Real.log N + (Real.log 4 + 4) * N := by
    calc (N : ℝ) * (∑ d ∈ Finset.Ioc 0 N, Λ d / d)
        = ((N : ℝ) * (∑ d ∈ Finset.Ioc 0 N, Λ d / d)
            - ∑ d ∈ Finset.Ioc 0 N, Λ d) + ∑ d ∈ Finset.Ioc 0 N, Λ d := by ring
      _ ≤ (N : ℝ) * Real.log N + (Real.log 4 + 4) * N := by
            have := hlow.trans hstep1
            linarith [hpsi]
  -- divide through by N > 0
  rw [← le_div_iff₀' hNr] at hcomb
  have heq : ((N : ℝ) * Real.log N + (Real.log 4 + 4) * N) / N
      = Real.log N + (Real.log 4 + 4) := by
    field_simp
  exact hcomb.trans (le_of_eq heq)

/-! ### Restricting to primes -/

/-- The prime `Nat`s in `range (N+1)` are exactly those in `Ioc 0 N`. -/
theorem filter_prime_range_eq_Ioc (N : ℕ) :
    (Finset.range (N + 1)).filter Nat.Prime = (Finset.Ioc 0 N).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨hlt, hp⟩; exact ⟨⟨hp.pos, by omega⟩, hp⟩
  · rintro ⟨⟨_, hle⟩, hp⟩; exact ⟨by omega, hp⟩

/-- **Mertens' first theorem, upper bound.**
`Σ_{p ≤ N} (log p)/p ≤ log N + (log 4 + 4)`, for `1 ≤ N`. -/
theorem sum_log_div_prime_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / p
      ≤ Real.log N + (Real.log 4 + 4) := by
  rw [filter_prime_range_eq_Ioc]
  refine le_trans ?_ (sum_vonMangoldt_div_le hN)
  -- prime subsum of `Λ d / d`, all terms nonneg
  have hsub : (Finset.Ioc 0 N).filter Nat.Prime ⊆ Finset.Ioc 0 N := Finset.filter_subset _ _
  have hcongr : ∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, Real.log p / p
      = ∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, Λ p / p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2]
  rw [hcongr]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro d _ _
  have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  positivity

/-! ## Step 5 — Abel summation to `Σ 1/p` -/

open MeasureTheory Set intervalIntegral

/-- The Abel-summation weight `f t = 1/log t`. -/
noncomputable def mF (t : ℝ) : ℝ := (Real.log t)⁻¹

/-- The Abel-summation coefficient sequence `c k = (log k)/k · [k prime]`. -/
noncomputable def mC (k : ℕ) : ℝ := if k.Prime then Real.log k / k else 0

theorem mC_zero : mC 0 = 0 := by simp [mC, Nat.not_prime_zero]

theorem mC_one : mC 1 = 0 := by simp [mC, Nat.not_prime_one]

theorem mC_nonneg (k : ℕ) : 0 ≤ mC k := by
  unfold mC
  split
  · rename_i hp
    have : (1 : ℝ) ≤ k := by exact_mod_cast hp.one_lt.le
    have h0 : (0 : ℝ) ≤ Real.log k := Real.log_nonneg this
    positivity
  · exact le_refl 0

/-- `f t = 1/log t` has derivative `-(t·(log t)²)⁻¹` for `t ≥ 2`. -/
theorem hasDerivAt_mF {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt mF (-(x * Real.log x ^ 2)⁻¹) x := by
  have hx0 : x ≠ 0 := by positivity
  have hxlog : Real.log x ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
  have h2 : HasDerivAt (fun t => (Real.log t)⁻¹) (-x⁻¹ / (Real.log x) ^ 2) x := h1.inv hxlog
  have heq : -x⁻¹ / (Real.log x) ^ 2 = -(x * Real.log x ^ 2)⁻¹ := by
    field_simp
  rw [heq] at h2
  exact h2

theorem differentiableAt_mF {x : ℝ} (hx : 2 ≤ x) : DifferentiableAt ℝ mF x :=
  (hasDerivAt_mF hx).differentiableAt

theorem deriv_mF {x : ℝ} (hx : 2 ≤ x) : deriv mF x = -(x * Real.log x ^ 2)⁻¹ :=
  (hasDerivAt_mF hx).deriv

/-- On `[2, N]`, `deriv mF` agrees with the continuous function
`t ↦ -(t·(log t)²)⁻¹`, hence is integrable there. -/
theorem integrableOn_deriv_mF (N : ℕ) :
    IntegrableOn (deriv mF) (Set.Icc 2 (N : ℝ)) := by
  have hne0 : ∀ t ∈ Set.Icc (2 : ℝ) N, t ≠ 0 := by
    intro t ht; simp only [Set.mem_Icc] at ht; linarith [ht.1]
  have hcont : ContinuousOn (fun t : ℝ => -(t * Real.log t ^ 2)⁻¹) (Set.Icc 2 (N : ℝ)) := by
    have hlogcont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc 2 (N : ℝ)) :=
      continuousOn_id.log hne0
    have hbase : ContinuousOn (fun t : ℝ => t * Real.log t ^ 2) (Set.Icc 2 (N : ℝ)) :=
      continuousOn_id.mul (hlogcont.pow 2)
    apply ContinuousOn.neg
    apply hbase.inv₀
    intro t ht
    simp only [Set.mem_Icc] at ht
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    positivity
  have hint : IntegrableOn (fun t : ℝ => -(t * Real.log t ^ 2)⁻¹) (Set.Icc 2 (N : ℝ)) :=
    hcont.integrableOn_compact isCompact_Icc
  apply hint.congr_fun _ measurableSet_Icc
  intro t ht
  simp only [Set.mem_Icc] at ht
  rw [deriv_mF ht.1]

/-- Prime-sum form of the partial sums `Σ_{k≤M} c k`. -/
theorem sum_mC_Icc_eq (M : ℕ) :
    ∑ k ∈ Finset.Icc 0 M, mC k
      = ∑ p ∈ (Finset.range (M + 1)).filter Nat.Prime, Real.log p / p := by
  have hset : (Finset.Icc 0 M) = Finset.range (M + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_range]; omega
  rw [hset]
  unfold mC
  rw [Finset.sum_filter]

theorem sum_mC_Icc_nonneg (M : ℕ) : 0 ≤ ∑ k ∈ Finset.Icc 0 M, mC k :=
  Finset.sum_nonneg (fun k _ => mC_nonneg k)

/-- The Step-4 bound, in the `Σ c` shape used by Abel summation. -/
theorem sum_mC_Icc_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Icc 0 M, mC k ≤ Real.log M + (Real.log 4 + 4) := by
  rw [sum_mC_Icc_eq]
  exact sum_log_div_prime_le hM

/-! ### The two elementary integrals -/

/-- `t ↦ 1/(t·log t)` is continuous on `[2, N]`. -/
theorem continuousOn_inv_tlog {N : ℕ} (hN : 2 ≤ N) :
    ContinuousOn (fun t : ℝ => (t * Real.log t)⁻¹) (Set.uIcc 2 (N : ℝ)) := by
  have hle : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Set.uIcc_of_le hle]
  have hne0 : ∀ t ∈ Set.Icc (2 : ℝ) N, t ≠ 0 := by
    intro t ht; simp only [Set.mem_Icc] at ht; linarith [ht.1]
  apply ContinuousOn.inv₀ (continuousOn_id.mul (continuousOn_id.log hne0))
  intro t ht
  simp only [Set.mem_Icc] at ht
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  have ht0 : (0 : ℝ) < t := by linarith [ht.1]
  exact mul_ne_zero ht0.ne' hlog

/-- `t ↦ 1/(t·(log t)²)` is continuous on `[2, N]`. -/
theorem continuousOn_inv_tlogsq {N : ℕ} (hN : 2 ≤ N) :
    ContinuousOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Set.uIcc 2 (N : ℝ)) := by
  have hle : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Set.uIcc_of_le hle]
  have hne0 : ∀ t ∈ Set.Icc (2 : ℝ) N, t ≠ 0 := by
    intro t ht; simp only [Set.mem_Icc] at ht; linarith [ht.1]
  apply ContinuousOn.inv₀ (continuousOn_id.mul ((continuousOn_id.log hne0).pow 2))
  intro t ht
  simp only [Set.mem_Icc] at ht
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  have ht0 : (0 : ℝ) < t := by linarith [ht.1]
  exact mul_ne_zero ht0.ne' (pow_ne_zero 2 hlog)

/-- `∫₂^N 1/(t·log t) dt = log log N − log log 2`. -/
theorem integral_inv_tlog {N : ℕ} (hN : 2 ≤ N) :
    ∫ t in (2 : ℝ)..N, (t * Real.log t)⁻¹
      = Real.log (Real.log N) - Real.log (Real.log 2) := by
  have hle : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hcont := continuousOn_inv_tlog hN
  have hderiv : ∀ x ∈ Set.uIcc (2 : ℝ) N,
      HasDerivAt (fun t => Real.log (Real.log t)) ((x * Real.log x)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hle, Set.mem_Icc] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
    have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
    have hinner : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    have houter : HasDerivAt Real.log (Real.log x)⁻¹ (Real.log x) := Real.hasDerivAt_log hlogne
    have hcomp := houter.comp x hinner
    have hval : (Real.log x)⁻¹ * x⁻¹ = (x * Real.log x)⁻¹ := by rw [mul_inv]; ring
    rw [hval] at hcomp
    exact hcomp
  have key := integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  simpa using key

/-- `∫₂^N 1/(t·(log t)²) dt = 1/log 2 − 1/log N`. -/
theorem integral_inv_tlogsq {N : ℕ} (hN : 2 ≤ N) :
    ∫ t in (2 : ℝ)..N, (t * Real.log t ^ 2)⁻¹
      = (Real.log 2)⁻¹ - (Real.log N)⁻¹ := by
  have hle : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hcont := continuousOn_inv_tlogsq hN
  have hderiv : ∀ x ∈ Set.uIcc (2 : ℝ) N,
      HasDerivAt (fun t => -(Real.log t)⁻¹) ((x * Real.log x ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hle, Set.mem_Icc] at hx
    have hx2 : (2 : ℝ) ≤ x := hx.1
    have h := (hasDerivAt_mF hx2).neg
    rwa [neg_neg] at h
  have key := integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [key]; ring

/-! ### Main assembly -/

/-- **Mertens' 2nd theorem, upper bound (core estimate).**
For `2 ≤ N`, `Σ_{p ≤ N} 1/p ≤ log log N + C₀` with the explicit constant
`C₀ = 1 + 2·(log 4 + 4)/log 2 − log log 2`. -/
theorem sum_inv_prime_le_aux {N : ℕ} (hN : 2 ≤ N) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / p
      ≤ Real.log (Real.log N)
        + (1 + 2 * (Real.log 4 + 4) / Real.log 2 - Real.log (Real.log 2)) := by
  have hle : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogNpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog2N : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hle
  set c₀ : ℝ := Real.log 4 + 4 with hc₀
  have hc₀nn : 0 ≤ c₀ := by
    rw [hc₀]; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  -- Abel summation
  have habel := sum_mul_eq_sub_integral_mul₁ mC mC_zero mC_one (N : ℝ)
    (fun t ht => differentiableAt_mF (by simp only [Set.mem_Icc] at ht; exact ht.1))
    (integrableOn_deriv_mF N)
  rw [Nat.floor_natCast] at habel
  -- LHS of Abel = Σ_{p≤N} 1/p
  have hLHS : ∑ k ∈ Finset.Icc 0 N, mF k * mC k
      = ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / p := by
    have hIcc : (Finset.Icc 0 N) = Finset.range (N + 1) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_range]; omega
    rw [hIcc, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    unfold mF mC
    by_cases hk : k.Prime
    · simp only [hk, if_true]
      have hk2 : (1 : ℝ) < k := by exact_mod_cast hk.one_lt
      have hlogk : Real.log k ≠ 0 := ne_of_gt (Real.log_pos hk2)
      field_simp
    · simp only [hk, if_false, mul_zero]
  rw [hLHS] at habel
  rw [habel]
  set B : ℝ := ∑ k ∈ Finset.Icc 0 N, mC k with hB
  have hBle : B ≤ Real.log N + c₀ := sum_mC_Icc_le (by omega)
  have hBnn : 0 ≤ B := sum_mC_Icc_nonneg N
  -- Term 1: `mF N · B ≤ 1 + c₀/log 2`
  have hT1 : mF (N : ℝ) * B ≤ 1 + c₀ / Real.log 2 := by
    have hmul : mF (N : ℝ) * B ≤ (Real.log N)⁻¹ * (Real.log N + c₀) := by
      rw [mF]; exact mul_le_mul_of_nonneg_left hBle (by positivity)
    have hsimp : (Real.log N)⁻¹ * (Real.log N + c₀) = 1 + c₀ / Real.log N := by
      field_simp
    have hfrac : c₀ / Real.log N ≤ c₀ / Real.log 2 :=
      div_le_div_of_nonneg_left hc₀nn hlog2pos hlog2N
    rw [hsimp] at hmul; linarith
  -- The Abel integrand
  set S : ℝ → ℝ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k with hS
  -- Integrability of the two integrands over `Ioc 2 N`
  have hgint : IntegrableOn (fun t => deriv mF t * S t) (Set.Ioc 2 (N : ℝ)) :=
    (integrableOn_mul_sum_Icc mC (m := 0) (by norm_num) (integrableOn_deriv_mF N)).mono_set
      Set.Ioc_subset_Icc_self
  have hUcont : ContinuousOn
      (fun t : ℝ => (t * Real.log t ^ 2)⁻¹ * (Real.log t + c₀)) (Set.Icc 2 (N : ℝ)) := by
    have h1 : ContinuousOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Set.Icc 2 (N : ℝ)) := by
      have := continuousOn_inv_tlogsq hN; rwa [Set.uIcc_of_le hle] at this
    have hne0 : ∀ t ∈ Set.Icc (2 : ℝ) N, t ≠ 0 := by
      intro t ht; simp only [Set.mem_Icc] at ht; linarith [ht.1]
    exact h1.mul ((continuousOn_id.log hne0).add continuousOn_const)
  have hUint : IntegrableOn
      (fun t : ℝ => (t * Real.log t ^ 2)⁻¹ * (Real.log t + c₀)) (Set.Ioc 2 (N : ℝ)) :=
    (hUcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  -- Pointwise bound `-U ≤ deriv mF · S` on `Ioc 2 N`
  have hpt : ∀ t ∈ Set.Ioc 2 (N : ℝ),
      -((t * Real.log t ^ 2)⁻¹ * (Real.log t + c₀)) ≤ deriv mF t * S t := by
    intro t ht
    simp only [Set.mem_Ioc] at ht
    have ht2 : (2 : ℝ) ≤ t := le_of_lt ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hinvnn : (0 : ℝ) ≤ (t * Real.log t ^ 2)⁻¹ := by positivity
    -- `S t ≤ log t + c₀`
    have hfloor1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ t))
    have hfloorpos : (0 : ℝ) < (⌊t⌋₊ : ℝ) := by exact_mod_cast hfloor1
    have hSbound : S t ≤ Real.log t + c₀ := by
      rw [hS]
      refine (sum_mC_Icc_le hfloor1).trans ?_
      have : Real.log (⌊t⌋₊ : ℝ) ≤ Real.log t :=
        Real.log_le_log hfloorpos (Nat.floor_le ht0.le)
      linarith
    have hderiv : deriv mF t = -(t * Real.log t ^ 2)⁻¹ := deriv_mF ht2
    rw [hderiv]
    have hkey : (t * Real.log t ^ 2)⁻¹ * S t
        ≤ (t * Real.log t ^ 2)⁻¹ * (Real.log t + c₀) :=
      mul_le_mul_of_nonneg_left hSbound hinvnn
    nlinarith [hkey]
  -- ⇒  `∫(-U) ≤ ∫ deriv mF · S`
  have hmono : (∫ t in Set.Ioc 2 (N : ℝ), -((t * Real.log t ^ 2)⁻¹ * (Real.log t + c₀)))
      ≤ ∫ t in Set.Ioc 2 (N : ℝ), deriv mF t * S t := by
    refine setIntegral_mono_on ?_ hgint measurableSet_Ioc hpt
    exact hUint.neg
  rw [MeasureTheory.integral_neg] at hmono
  -- Evaluate `∫U`
  have hUeval : ∫ t in Set.Ioc 2 (N : ℝ), (t * Real.log t ^ 2)⁻¹ * (Real.log t + c₀)
      = (Real.log (Real.log N) - Real.log (Real.log 2))
        + c₀ * ((Real.log 2)⁻¹ - (Real.log N)⁻¹) := by
    rw [← intervalIntegral.integral_of_le hle]
    have hsplit : ∫ t in (2 : ℝ)..N, (t * Real.log t ^ 2)⁻¹ * (Real.log t + c₀)
        = ∫ t in (2 : ℝ)..N, ((t * Real.log t)⁻¹ + c₀ * (t * Real.log t ^ 2)⁻¹) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hle, Set.mem_Icc] at ht
      have ht0 : (0 : ℝ) < t := by linarith [ht.1]
      have hlog : Real.log t ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
      field_simp
    rw [hsplit, intervalIntegral.integral_add (continuousOn_inv_tlog hN).intervalIntegrable
      ((continuousOn_inv_tlogsq hN).intervalIntegrable.const_mul c₀),
      intervalIntegral.integral_const_mul, integral_inv_tlog hN, integral_inv_tlogsq hN]
  -- Combine everything
  have hIbound : -(∫ t in Set.Ioc 2 (N : ℝ), deriv mF t * S t)
      ≤ (Real.log (Real.log N) - Real.log (Real.log 2))
        + c₀ * ((Real.log 2)⁻¹ - (Real.log N)⁻¹) := by
    rw [← hUeval]; linarith [hmono]
  have hcNpos : 0 ≤ c₀ * (Real.log N)⁻¹ := by positivity
  have hc2 : c₀ * (Real.log 2)⁻¹ = c₀ / Real.log 2 := by rw [div_eq_mul_inv]
  -- final numeric chain
  have hmix : c₀ * ((Real.log 2)⁻¹ - (Real.log N)⁻¹) ≤ c₀ / Real.log 2 := by
    rw [mul_sub, hc2]; linarith [hcNpos]
  -- align the goal's integral (explicit sum) with `S`, and split `2·c₀/log2`
  have hInt_eq : (∫ t in Set.Ioc 2 (N : ℝ),
        deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      = ∫ t in Set.Ioc 2 (N : ℝ), deriv mF t * S t := rfl
  rw [hInt_eq, mul_div_assoc]
  linarith [hT1, hIbound, hmix]

/-- **Mertens' 2nd theorem, upper bound.** `Σ_{p ≤ x} 1/p ≤ log log x + C`.
Only the upper direction is needed downstream (N3.4 → N5.2). -/
theorem sum_inv_prime_le :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p
        ≤ Real.log (Real.log n) + C :=
  ⟨1 + 2 * (Real.log 4 + 4) / Real.log 2 - Real.log (Real.log 2),
    fun _n hn => sum_inv_prime_le_aux hn⟩

/-- Telescoping bound `Σ_{k=2}^{m} (1/(k−1) − 1/k) = 1 − 1/m`. -/
theorem sum_Icc_telescope {m : ℕ} (hm : 2 ≤ m) :
    ∑ k ∈ Finset.Icc 2 m, ((1 : ℝ) / ((k : ℝ) - 1) - 1 / k) = 1 - 1 / m := by
  induction m, hm using Nat.le_induction with
  | base => rw [Finset.Icc_self, Finset.sum_singleton]; norm_num
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hm0 : (0 : ℝ) < m := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hm0' : (m : ℝ) ≠ 0 := ne_of_gt hm0
    have hm1' : (m : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    rw [show ((m : ℝ) + 1 - 1) = (m : ℝ) by ring]
    field_simp
    ring

/-- `Σ_{p ≤ n} 1/(p−1) ≤ log log n + C'`. Since `1/(p−1) = 1/p + 1/(p(p−1))`
and `Σ_{k≥2} 1/(k(k−1))` telescopes to `≤ 1`, this follows from
`sum_inv_prime_le` with `C' = C + 1` (the brute `1/(p−1) ≤ 2/p` termwise
bound only gives `2·log log n`, so is not used). -/
theorem sum_inv_prime_sub_one_le :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / (p - 1)
        ≤ Real.log (Real.log n) + C := by
  obtain ⟨C, hC⟩ := sum_inv_prime_le
  refine ⟨C + 1, fun n hn => ?_⟩
  have hmain := hC n hn
  -- split `1/(p−1) = 1/p + (1/(p−1) − 1/p)`
  have hsplit : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / (p - 1)
      = (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p)
        + ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
            ((1 : ℝ) / ((p : ℝ) - 1) - 1 / p) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [hsplit]
  -- tail `≤ 1` via telescoping
  have htail : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
      ((1 : ℝ) / ((p : ℝ) - 1) - 1 / p) ≤ 1 := by
    have hsub : (Finset.range (n + 1)).filter Nat.Prime ⊆ Finset.Icc 2 n := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_Icc]
      exact ⟨hp.2.two_le, by omega⟩
    have hnn : ∀ k ∈ Finset.Icc 2 n, 0 ≤ (1 : ℝ) / ((k : ℝ) - 1) - 1 / k := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
      have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
      have hkk : (k : ℝ) - 1 ≤ k := by linarith
      have := one_div_le_one_div_of_le hk1 hkk
      linarith
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => hnn k hk)).trans ?_
    rw [sum_Icc_telescope hn]
    have hnpos : (0 : ℝ) < n := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  linarith [hmain, htail]

end Salt.Maynard

end




section
open Finset ArithmeticFunction

theorem solution (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n
      = ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  apply Salt.Maynard.sum_log_eq_sum_vonMangoldt_mul_div <;> assumption

end

