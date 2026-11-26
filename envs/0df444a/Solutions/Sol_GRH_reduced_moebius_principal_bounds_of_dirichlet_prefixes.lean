-- Prove2me | solution 1 for GRH.reduced_moebius_principal_bounds_of_dirichlet_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T11:54:03.114304+00:00
-- url     : https://prove2.me/submissions/e036cdd7-d539-4316-a694-3190ee05ff4e

import Theorems.Thm_GRH_moebius_harmonic_decay_of_bounded_dirichlet_prefixes
import Theorems.Thm_GRH_liouville_harmonic_le_of_moebius_harmonic_le
import Theorems.Thm_GRH_reduced_liouville_harmonic_le_of_modulus_one
import Theorems.Thm_GRH_reduced_moebius_harmonic_le_of_liouville_harmonic_le
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/- The four harmonic transfer steps below follow the accepted proof
https://prove2.me/submissions/fb5b50f4-8dbf-495b-999d-76118ada7f21 .
Here a bounded prefix at the chosen exponent replaces its upper-range hypothesis. -/
open scoped BigOperators

private theorem sqrt_increment (k : ℕ) :
    (((k : ℝ)+1)^(1/2 : ℝ))⁻¹ ≤ 2*(Real.sqrt ((k:ℝ)+1)-Real.sqrt (k:ℝ)) := by
  rw [← Real.sqrt_eq_rpow]
  have hb : 0 < Real.sqrt ((k:ℝ)+1) := Real.sqrt_pos.2 (by positivity)
  have ha : Real.sqrt (k:ℝ) ≤ Real.sqrt ((k:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
  have hb2 := Real.sq_sqrt (show 0 ≤ (k:ℝ)+1 by positivity)
  have ha2 := Real.sq_sqrt (show 0 ≤ (k:ℝ) by positivity)
  rw [inv_eq_one_div, div_le_iff₀ hb]
  nlinarith [sq_nonneg (Real.sqrt ((k:ℝ)+1)-Real.sqrt (k:ℝ))]

private theorem sum_sqrt_inverses (n : ℕ) :
    (∑ k ∈ Finset.range n, (((k:ℝ)+1)^(1/2:ℝ))⁻¹) ≤ 2*Real.sqrt (n:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    linarith [sqrt_increment n]

private theorem sum_powers (n : ℕ) (σ : ℝ) (hs : (1/2:ℝ) ≤ σ) :
    (∑ k ∈ Finset.range n, ((k:ℝ)+1)^(σ-1)) ≤ 2*((n:ℝ)+1)^σ := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  let C := ((n:ℝ)+1)^(σ-1/2)
  have hC : 0 ≤ C := Real.rpow_nonneg hn.le _
  have each (k : ℕ) (hk : k ∈ Finset.range n) :
      ((k:ℝ)+1)^(σ-1) ≤ C*(((k:ℝ)+1)^(1/2:ℝ))⁻¹ := by
    have hk' : (k:ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
    have hk0 : 0 < (k:ℝ)+1 := by positivity
    have hm : ((k:ℝ)+1)^(σ-1/2) ≤ C := Real.rpow_le_rpow hk0.le (by linarith) (by linarith)
    calc
      _ = ((k:ℝ)+1)^(σ-1/2)*((k:ℝ)+1)^(-(1/2:ℝ)) := by
        rw [← Real.rpow_add hk0]; congr 1; ring
      _ ≤ _ := by rw [Real.rpow_neg hk0.le]; exact mul_le_mul_of_nonneg_right hm (by positivity)
  calc
    _ ≤ ∑ k ∈ Finset.range n, C*(((k:ℝ)+1)^(1/2:ℝ))⁻¹ := Finset.sum_le_sum each
    _ = C*(∑ k ∈ Finset.range n, (((k:ℝ)+1)^(1/2:ℝ))⁻¹) := (Finset.mul_sum ..).symm
    _ ≤ C*(2*Real.sqrt (n:ℝ)) := mul_le_mul_of_nonneg_left (sum_sqrt_inverses n) hC
    _ ≤ C*(2*Real.sqrt ((n:ℝ)+1)) := by gcongr; linarith
    _ = _ := by
      dsimp only [C]
      rw [Real.sqrt_eq_rpow, mul_left_comm, ← Real.rpow_add hn]
      congr 2
      ring

private theorem principal_of_harmonic (q : ℕ) [NeZero q] (σ K : ℝ) (hs : (1/2:ℝ) ≤ σ)
    (hK : 0 ≤ K) (hH : ∀ n : ℕ, |GRH.reducedMoebiusHarmonic q n| ≤ K*((n:ℝ)+1)^(σ-1)) :
    ∀ n : ℕ, |∑ k ∈ Finset.range (n+1),
      if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0|
        ≤ (3*K)*((n:ℝ)+1)^σ := by
  let H := GRH.reducedMoebiusHarmonic q
  let f := fun k : ℕ => if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0
  have step (k : ℕ) : H (k+1) = H k + f (k+1)/((k:ℝ)+1) := by
    dsimp only [H,f,GRH.reducedMoebiusHarmonic]
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le k)]
    simp only [Nat.cast_add, Nat.cast_one]
    by_cases hu : IsUnit ((k : ZMod q)+1) <;> simp [hu]
  have exact_sum (n : ℕ) : ∑ k ∈ Finset.range (n+1), f k =
      (n:ℝ)*H n - ∑ k ∈ Finset.range n, H k := by
    induction n with
    | zero => simp [f]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Nat.cast_succ, step]
      field_simp
      ring
  intro n
  change |∑ k ∈ Finset.range (n+1), f k| ≤ _
  rw [exact_sum]
  have hn : 0 < (n:ℝ)+1 := by positivity
  have h1 : |(n:ℝ)*H n| ≤ K*((n:ℝ)+1)^σ := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    calc
      _ ≤ (n:ℝ)*(K*((n:ℝ)+1)^(σ-1)) := mul_le_mul_of_nonneg_left (hH n) (Nat.cast_nonneg _)
      _ ≤ ((n:ℝ)+1)*(K*((n:ℝ)+1)^(σ-1)) := by gcongr; linarith
      _ = K*((n:ℝ)+1)^σ := by
        rw [mul_left_comm, mul_comm ((n:ℝ)+1) _, ← Real.rpow_add_one hn.ne']
        congr 2
        ring
  have h2 : |∑ k ∈ Finset.range n, H k| ≤ K*(2*((n:ℝ)+1)^σ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, |H k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, K*((k:ℝ)+1)^(σ-1) := Finset.sum_le_sum fun k _ => hH k
      _ = K*(∑ k ∈ Finset.range n, ((k:ℝ)+1)^(σ-1)) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_powers n σ hs) hK
  have h := (abs_sub ((n:ℝ)*H n) (∑ k ∈ Finset.range n, H k)).trans (add_le_add h1 h2)
  linarith


theorem solution
    (q : ℕ) [NeZero q] (σ B : ℝ) (hhalf : (1/2 : ℝ) < σ) (hone : σ < 1) (hB : 0 ≤ B)
    (hprefix : ∀ n : ℕ, |∑ j ∈ Finset.range n,
      (ArithmeticFunction.moebius j : ℝ) * (j : ℝ) ^ (-σ)| ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ n : ℕ, |GRH.reducedMoebiusHarmonic q n| ≤ K * ((n : ℝ) + 1) ^ (σ - 1)) ∧
      (∀ n : ℕ, |∑ k ∈ Finset.range (n + 1),
        if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0| ≤
        (3*K) * ((n : ℝ) + 1) ^ σ) := by
  let Z := ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹
  let D := ∑ d ∈ q.divisors, |(ArithmeticFunction.moebius d : ℝ)| * (d:ℝ)^(-σ)
  have hZ : 0 ≤ Z := tsum_nonneg fun d => by positivity
  have hD : 0 ≤ D := Finset.sum_nonneg fun d _ => by positivity
  let K := (((2*B)*Z)*D)*Z
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hH (U : ℕ) : |GRH.reducedMoebiusHarmonic q U| ≤ K*((U:ℝ)+1)^(σ-1) := by
    apply GRH.reduced_moebius_harmonic_le_of_liouville_harmonic_le q σ (((2*B)*Z)*D) hhalf hone.le (by positivity) _ U
    intro V
    apply GRH.reduced_liouville_harmonic_le_of_modulus_one q σ ((2*B)*Z) hone.le (by positivity) _ V
    intro W
    apply GRH.liouville_harmonic_le_of_moebius_harmonic_le σ (2*B) hhalf hone.le (by positivity) _ W
    exact GRH.moebius_harmonic_decay_of_bounded_dirichlet_prefixes σ B hone.le hB hprefix
  exact ⟨K,hK,hH,principal_of_harmonic q σ K hhalf.le hK hH⟩
