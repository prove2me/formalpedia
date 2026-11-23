-- Prove2me | solution 1 for BroughanRH.kaneko
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:59:29.403872+00:00
-- url     : https://prove2.me/submissions/c9bf24d4-ead1-40a4-946e-8423a7bd0b1f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BroughanRH_robin
import Theorems.Thm_LeanEval_NumberTheory_lagarias_harmonic_lower_bound
import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace KanekoFinite

def expLower (q : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 30, q ^ i / (Nat.factorial i : ℝ)

def logLower (q : ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range 12, ((q-1)/(q+1)) ^ (2*i+1) / (2*i+1 : ℝ)

lemma rhs_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    Real.exp x * Real.log x ≤ Real.exp y * Real.log y :=
  mul_le_mul (Real.exp_le_exp.mpr hxy) (Real.log_le_log (by linarith) hxy) (Real.log_nonneg hx)
    (Real.exp_nonneg y)

lemma lower_le {q : ℝ} (hq : 1 ≤ q) :
    expLower q * logLower q ≤ Real.exp q * Real.log q := by
  have hp : 0 < q+1 := by linarith
  have ht₀ : 0 ≤ (q-1)/(q+1) := div_nonneg (by linarith) hp.le
  have ht₁ : (q-1)/(q+1) < 1 := (div_lt_one hp).mpr (by linarith)
  have hid : (1+(q-1)/(q+1))/(1-(q-1)/(q+1)) = q := by
    field_simp
    ring
  have hl := Real.sum_range_le_log_div ht₀ ht₁ 12
  rw [hid] at hl
  have hl' : logLower q ≤ Real.log q := by unfold logLower; linarith
  have hl₀ : 0 ≤ logLower q := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    exact div_nonneg (pow_nonneg ht₀ _) (by positivity)
  have he : expLower q ≤ Real.exp q := Real.sum_le_exp_of_nonneg (by linarith) 30
  exact mul_le_mul he hl' hl₀ (Real.exp_nonneg q)

def floorH (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 1000000 / (i+1)

lemma floorH_le (n : ℕ) :
    (floorH n : ℝ) / 1000000 ≤ (harmonic n : ℝ) := by
  calc
    _ = ∑ i ∈ Finset.range n, ((1000000 / (i+1) : ℕ) : ℝ) / 1000000 := by
      simp [floorH,Finset.sum_div]
    _ ≤ ∑ i ∈ Finset.range n, (((i+1 : ℕ) : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      have h : ((1000000 / (i+1) : ℕ) : ℝ) ≤ (1000000 : ℝ) / (i+1 : ℕ) :=
        Nat.cast_div_le
      calc
        _ ≤ ((1000000 : ℝ) / (i+1 : ℕ)) / 1000000 :=
          div_le_div_of_nonneg_right h (by norm_num)
        _ = _ := by push_cast; field_simp
    _ = (harmonic n : ℝ) := by simp [harmonic]

lemma harmonic_mono {n m : ℕ} (h : n ≤ m) :
    (harmonic n : ℝ) ≤ (harmonic m : ℝ) := by
  unfold harmonic
  push_cast
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    (fun i _ _ => inv_nonneg.mpr (by positivity))

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped ArithmeticFunction.sigma

/-- `(a, b, S, Q)`: for `a ≤ n < b`, `σ(n) ≤ S`, and `Q / 10^4 ≤ H_a`. -/
def checkpoints : List (ℕ × ℕ × ℕ × ℕ) := [
  (61,72,144,46962),
  (72,84,195,48607),
  (84,96,234,50139),
  (96,120,280,51467),
  (120,144,360,53688),
  (144,168,403,55504),
  (168,180,480,57040),
  (180,210,546,57728),
  (210,240,600,59266),
  (240,288,744,60598),
  (288,336,868,62417),
  (336,360,992,63956),
  (360,420,1170,64645),
  (420,480,1344,66184),
  (480,540,1560,67518),
  (540,600,1680,68694),
  (600,720,2016,69747),
  (720,840,2418,71568),
  (840,960,2880,73108),
  (960,1080,3224,74442),
  (1080,1260,3844,75619),
  (1260,1440,4368,77159),
  (1440,1680,5082,78492),
  (1680,1980,6120,80032),
  (1980,2160,6944,81673),
  (2160,2520,7812,82542),
  (2520,2880,9360,84082),
  (2880,3360,10890,85415),
  (3360,3780,12493,86954),
  (3780,4200,14040,88130),
  (4200,4680,16128,89181),
  (4680,5040,16380,90261),
  (5040,5041,19344,91000)
]

def fastSigma (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.primeFactorsList.count p + 1), p ^ i

lemma sigma_eq_fast (n : ℕ) (hn : n ≠ 0) : σ 1 n = fastSigma n := by
  simpa [fastSigma] using
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (k := 1) hn

lemma select_record (n : ℕ) (hn : 61 ≤ n) (hb : n ≤ 5040) :
    ∃ r ∈ checkpoints, r.1 ≤ n ∧ n < r.2.1 := by
  simp only [checkpoints, List.mem_cons, List.not_mem_nil, or_false,
    or_and_right, exists_or, exists_eq_left]
  omega

lemma intervals_checked :
    (checkpoints.all fun r =>
      (List.range' r.1 (r.2.1-r.1)).all fun n =>
        decide (fastSigma n ≤ r.2.2.1)) = true := by decide +kernel

lemma cover_cert (r : ℕ × ℕ × ℕ × ℕ) (hr : r ∈ checkpoints)
    (n : ℕ) (hn : 0 < n) (ha : r.1 ≤ n) (hb : n < r.2.1) :
    σ 1 n ≤ r.2.2.1 := by
  have h := List.all_eq_true.mp intervals_checked r hr
  have hm : n ∈ List.range' r.1 (r.2.1-r.1) := by
    apply List.mem_range'.mpr
    exact ⟨n-r.1, by omega, by omega⟩
  have hc : fastSigma n ≤ r.2.2.1 := of_decide_eq_true (List.all_eq_true.mp h n hm)
  rwa [sigma_eq_fast n (by omega)]

lemma floor_cert : ∀ r ∈ checkpoints,
    10000 ≤ r.2.2.2 ∧ r.2.2.2 * 100 ≤ floorH r.1 := by decide +kernel

lemma strict_cert : ∀ r ∈ checkpoints,
    (r.2.2.1 : ℝ) < expLower ((r.2.2.2 : ℝ)/10000) * logLower ((r.2.2.2 : ℝ)/10000) := by
  intro r hr
  simp only [checkpoints,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [expLower,logLower,Finset.sum_range_succ]

lemma finite_range {n : ℕ} (hn : 61 ≤ n) (hbound : n ≤ 5040) :
    ((σ 1 n : ℕ) : ℝ) ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  obtain ⟨r,hr,ha,hb⟩ := select_record n hn hbound
  have hs := cover_cert r hr n (by omega) ha hb
  obtain ⟨hq,hfloor⟩ := floor_cert r hr
  have hq₁ : 1 ≤ (r.2.2.2 : ℝ)/10000 := by
    apply (le_div_iff₀ (by norm_num)).mpr
    norm_num
    exact_mod_cast hq
  have hqH : (r.2.2.2 : ℝ)/10000 ≤ (harmonic n : ℝ) := by
    have hf : (r.2.2.2 : ℝ) * 100 ≤ (floorH r.1 : ℝ) := by exact_mod_cast hfloor
    have hqf : (r.2.2.2 : ℝ)/10000 ≤ (floorH r.1 : ℝ)/1000000 := by linarith
    exact hqf.trans ((floorH_le _).trans (harmonic_mono ha))
  have hs' : ((σ 1 n : ℕ) : ℝ) ≤ (r.2.2.1 : ℝ) := by exact_mod_cast hs
  exact (hs'.trans_lt ((strict_cert _ hr).trans_le
    ((lower_le hq₁).trans (rhs_mono hq₁ hqH)))).le

end KanekoFinite

end

theorem solution :
    ∀ n : ℕ, 60 < n → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  intro n hn
  rcases le_or_gt n 5040 with h | h
  · exact KanekoFinite.finite_range (by omega) h
  · have h1 := BroughanRH.robin n h
    have h2 := LeanEval.NumberTheory.lagarias_harmonic_lower_bound n (by omega)
    linarith
