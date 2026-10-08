-- Prove2me | solution 1 for GKP1998.besselK_decay_besselI_growth
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:42:29.997863+00:00
-- url     : https://prove2.me/submissions/10449eea-b448-4adb-8110-a6f4cb8f22b8

import Mathlib
import Definitions.Def_GKP1998_Defs

set_option autoImplicit false

open Filter Topology Asymptotics Nat

namespace GKP1998P

lemma one_add_sq_half_le_cosh (t : ℝ) : 1 + t ^ 2 / 2 ≤ Real.cosh t := by
  have h := Real.hasSum_cosh t
  have := sum_le_hasSum (Finset.range 2) (fun i _ => by
    apply div_nonneg _ (by positivity)
    rw [pow_mul]; positivity) h
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  linarith

lemma cosh_le_exp_of_nonneg {z : ℝ} (hz : 0 ≤ z) : Real.cosh z ≤ Real.exp z := by
  rw [Real.cosh_eq]
  have : Real.exp (-z) ≤ Real.exp z := Real.exp_le_exp.mpr (by linarith)
  linarith

lemma pointwise_bound (ν x t : ℝ) (hν : 0 ≤ ν) (hx : 1 ≤ x) (ht : 0 ≤ t) :
    ‖Real.exp (-x * Real.cosh t) * Real.cosh (ν * t)‖ ≤
      Real.exp (-x) * Real.exp ((ν + 1) ^ 2 / 2) * Real.exp (-t) := by
  have hc := one_add_sq_half_le_cosh t
  have hc1 := Real.one_le_cosh t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le)]
  calc Real.exp (-x * Real.cosh t) * Real.cosh (ν * t)
      ≤ Real.exp (-x * Real.cosh t) * Real.exp (ν * t) := by
        gcongr; exact cosh_le_exp_of_nonneg (mul_nonneg hν ht)
    _ = Real.exp (-x * Real.cosh t + ν * t) := by rw [Real.exp_add]
    _ ≤ Real.exp (-x + (ν + 1) ^ 2 / 2 + -t) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hc1), sq_nonneg (t - (ν + 1))]
    _ = _ := by rw [Real.exp_add, Real.exp_add]

lemma partA (ν : ℝ) (hν : 0 ≤ ν) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |GKP1998.besselK ν x| ≤ C * Real.exp (-x) := by
  refine ⟨Real.exp ((ν + 1) ^ 2 / 2), fun x hx => ?_⟩
  unfold GKP1998.besselK
  rw [← Real.norm_eq_abs]
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (-x) * Real.exp ((ν + 1) ^ 2 / 2) * Real.exp (-t)) (Set.Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).const_mul _
  refine (MeasureTheory.norm_integral_le_of_norm_le hint ?_).trans ?_
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    exact pointwise_bound ν x t hν hx (le_of_lt ht)
  · rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi_zero]
    exact le_of_eq (by ring)

lemma nat_fact_bound (j N : ℕ) : j ! * (j + N)! ≤ N ! * 2 ^ N * 4 ^ j * (2 * j)! := by
  have h1 : (j + N)! ≤ 2 ^ (j + N) * j ! * N ! := by
    rw [← Nat.add_choose_mul_factorial_mul_factorial j N, Nat.mul_assoc, Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
  have h2 : j ! * j ! ≤ (2 * j)! := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add j j
    rw [two_mul]; exact Nat.le_of_dvd (Nat.factorial_pos _) this
  have h4 : 2 ^ j ≤ 4 ^ j := Nat.pow_le_pow_left (by norm_num) j
  calc j ! * (j + N)! ≤ j ! * (2 ^ (j + N) * j ! * N !) := Nat.mul_le_mul_left _ h1
    _ = N ! * 2 ^ N * 2 ^ j * (j ! * j !) := by rw [pow_add]; ring
    _ ≤ N ! * 2 ^ N * 4 ^ j * (2 * j)! := by gcongr

lemma gamma_le_fact (ν : ℝ) (hν : 0 ≤ ν) (j : ℕ) :
    Real.Gamma ((j : ℝ) + ν + 1) ≤ ((j + ⌈ν⌉₊)! : ℝ) := by
  have hN : ν ≤ (⌈ν⌉₊ : ℝ) := Nat.le_ceil ν
  have hj : (0 : ℝ) ≤ j := j.cast_nonneg
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have h2 : ((j + ⌈ν⌉₊ : ℕ) : ℝ) + 1 ∈ Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_Ioi]; positivity
  have hz : (j : ℝ) + ν + 1 ∈ segment ℝ (1 : ℝ) (((j + ⌈ν⌉₊ : ℕ) : ℝ) + 1) := by
    rw [segment_eq_Icc (by push_cast; linarith)]
    constructor <;> push_cast <;> linarith
  have := Real.convexOn_Gamma.le_on_segment h1 h2 hz
  rw [Real.Gamma_one, Real.Gamma_nat_eq_factorial] at this
  refine this.trans (max_le ?_ le_rfl)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)

lemma rpow_split {y : ℝ} (hy : 0 < y) (j : ℕ) (ν : ℝ) :
    y ^ (2 * (j : ℝ) + ν) = y ^ (2 * j) * y ^ ν := by
  rw [Real.rpow_add hy, show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

lemma inv_gamma_le (ν : ℝ) (hν : 0 ≤ ν) (j : ℕ) :
    1 / Real.Gamma ((j : ℝ) + ν + 1) ≤ 1 / Real.Gamma (ν + 1) + 1 := by
  have hG0 := Real.Gamma_pos_of_pos (show 0 < ν + 1 by linarith)
  have h0 : 0 ≤ 1 / Real.Gamma (ν + 1) := by positivity
  rcases j with _ | j
  · simp
  · have hpos : 0 < Real.Gamma (((j + 1 : ℕ) : ℝ) + ν + 1) :=
      Real.Gamma_pos_of_pos (by positivity)
    have hj : (0 : ℝ) ≤ j := j.cast_nonneg
    have h2 : 1 ≤ Real.Gamma (((j + 1 : ℕ) : ℝ) + ν + 1) := by
      have := Real.Gamma_strictMonoOn_Ici.monotoneOn (a := 2)
        (b := ((j + 1 : ℕ) : ℝ) + ν + 1) (by simp)
        (by simp only [Set.mem_Ici]; push_cast; linarith) (by push_cast; linarith)
      rwa [Real.Gamma_two] at this
    have : 1 / Real.Gamma (((j + 1 : ℕ) : ℝ) + ν + 1) ≤ 1 := by
      rw [div_le_one hpos]; exact h2
    linarith

lemma besselI_summable (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ} (hx : 0 < x) :
    Summable (fun j : ℕ => (x / 2) ^ (2 * (j : ℝ) + ν) /
      ((j.factorial : ℝ) * Real.Gamma ((j : ℝ) + ν + 1))) := by
  have hy : 0 < x / 2 := by positivity
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
    ((Real.summable_pow_div_factorial ((x / 2) ^ 2)).mul_left
      ((x / 2) ^ ν * (1 / Real.Gamma (ν + 1) + 1)))
  · have := Real.Gamma_pos_of_pos (show 0 < (j : ℝ) + ν + 1 by positivity)
    positivity
  · have hg := Real.Gamma_pos_of_pos (show 0 < (j : ℝ) + ν + 1 by positivity)
    have hb := inv_gamma_le ν hν j
    have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    rw [rpow_split hy, ← pow_mul]
    calc (x / 2) ^ (2 * j) * (x / 2) ^ ν / ((j.factorial : ℝ) * Real.Gamma ((j : ℝ) + ν + 1))
        = (x / 2) ^ ν * (1 / Real.Gamma ((j : ℝ) + ν + 1)) *
            ((x / 2) ^ (2 * j) / j.factorial) := by
          field_simp
      _ ≤ (x / 2) ^ ν * (1 / Real.Gamma (ν + 1) + 1) * ((x / 2) ^ (2 * j) / j.factorial) := by
          gcongr

lemma term_lower (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ} (hx : 2 ≤ x) (j : ℕ) :
    1 / ((⌈ν⌉₊ ! : ℝ) * 2 ^ ⌈ν⌉₊) * ((x / 4) ^ (2 * j) / ((2 * j)! : ℝ)) ≤
      (x / 2) ^ (2 * (j : ℝ) + ν) / ((j.factorial : ℝ) * Real.Gamma ((j : ℝ) + ν + 1)) := by
  set N := ⌈ν⌉₊ with hNdef
  have hy : 0 < x / 2 := by linarith
  have hg := Real.Gamma_pos_of_pos (show 0 < (j : ℝ) + ν + 1 by positivity)
  have hgl := gamma_le_fact ν hν j
  rw [← hNdef] at hgl
  have hnat : ((j ! * (j + N)! : ℕ) : ℝ) ≤ ((N ! * 2 ^ N * 4 ^ j * (2 * j)! : ℕ) : ℝ) := by
    exact_mod_cast nat_fact_bound j N
  push_cast at hnat
  have hfj : (0 : ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
  have hden : (j ! : ℝ) * Real.Gamma ((j : ℝ) + ν + 1) ≤
      (N ! : ℝ) * 2 ^ N * 4 ^ j * ((2 * j)! : ℝ) :=
    (mul_le_mul_of_nonneg_left hgl hfj.le).trans hnat
  have hrp : 1 ≤ (x / 2) ^ ν := Real.one_le_rpow (by linarith) hν
  rw [rpow_split hy]
  have hx4 : (x / 4) ^ (2 * j) = (x / 2) ^ (2 * j) / 4 ^ j := by
    rw [pow_mul, pow_mul, show (x / 2) ^ 2 = (x / 4) ^ 2 * 4 by ring, mul_pow]
    field_simp
  have hA : 0 ≤ (x / 2) ^ (2 * j) := by positivity
  have hpos : 0 < (j ! : ℝ) * Real.Gamma ((j : ℝ) + ν + 1) := mul_pos hfj hg
  have hf2 : (0 : ℝ) < ((2 * j)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  calc 1 / ((N ! : ℝ) * 2 ^ N) * ((x / 4) ^ (2 * j) / ((2 * j)! : ℝ))
      = (x / 2) ^ (2 * j) / ((N ! : ℝ) * 2 ^ N * 4 ^ j * ((2 * j)! : ℝ)) := by
        rw [hx4]; field_simp
    _ ≤ (x / 2) ^ (2 * j) / ((j ! : ℝ) * Real.Gamma ((j : ℝ) + ν + 1)) :=
        div_le_div_of_nonneg_left hA hpos hden
    _ ≤ (x / 2) ^ (2 * j) * (x / 2) ^ ν / ((j ! : ℝ) * Real.Gamma ((j : ℝ) + ν + 1)) :=
        div_le_div_of_nonneg_right (le_mul_of_one_le_right hA hrp) hpos.le

lemma besselI_lower (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ} (hx : 2 ≤ x) :
    1 / ((⌈ν⌉₊ ! : ℝ) * 2 ^ ⌈ν⌉₊) * (Real.exp (x / 4) / 2) ≤ GKP1998.besselI ν x := by
  have hs := besselI_summable ν hν (by linarith : (0 : ℝ) < x)
  have hc := (Real.hasSum_cosh (x / 4)).mul_left (1 / ((⌈ν⌉₊ ! : ℝ) * 2 ^ ⌈ν⌉₊))
  have h1 : 1 / ((⌈ν⌉₊ ! : ℝ) * 2 ^ ⌈ν⌉₊) * Real.cosh (x / 4) ≤ GKP1998.besselI ν x :=
    hasSum_le (fun j => term_lower ν hν hx j) hc hs.hasSum
  have h2 : Real.exp (x / 4) / 2 ≤ Real.cosh (x / 4) := by
    rw [Real.cosh_eq]; have := Real.exp_pos (-(x / 4)); linarith
  have h3 : 0 ≤ 1 / ((⌈ν⌉₊ ! : ℝ) * 2 ^ ⌈ν⌉₊) := by positivity
  exact (mul_le_mul_of_nonneg_left h2 h3).trans h1

lemma partB (ν : ℝ) (hν : 0 ≤ ν) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun x => Real.exp (-c * x) * GKP1998.besselI ν x) atTop atTop := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  have ha0 : 0 < 1 / ((⌈ν⌉₊ ! : ℝ) * 2 ^ ⌈ν⌉₊) := by positivity
  have hlim : Tendsto (fun x : ℝ => 1 / ((⌈ν⌉₊ ! : ℝ) * 2 ^ ⌈ν⌉₊) / 2 * Real.exp (x / 8))
      atTop atTop :=
    Tendsto.const_mul_atTop (by positivity)
      (Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num)))
  refine tendsto_atTop_mono' atTop ?_ hlim
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hb := besselI_lower ν hν hx
  have he : 0 < Real.exp (-(1 / 8) * x) := Real.exp_pos _
  have hee : Real.exp (-(1 / 8) * x) * Real.exp (x / 4) = Real.exp (x / 8) := by
    rw [← Real.exp_add]; congr 1; ring
  calc 1 / ((⌈ν⌉₊ ! : ℝ) * 2 ^ ⌈ν⌉₊) / 2 * Real.exp (x / 8)
      = Real.exp (-(1 / 8) * x) * (1 / ((⌈ν⌉₊ ! : ℝ) * 2 ^ ⌈ν⌉₊) * (Real.exp (x / 4) / 2)) := by
        rw [← hee]; ring
    _ ≤ Real.exp (-(1 / 8) * x) * GKP1998.besselI ν x := mul_le_mul_of_nonneg_left hb he.le

end GKP1998P

open Filter Topology Asymptotics GKP1998 in
theorem solution (ν : ℝ) (hν : 0 ≤ ν) :
    (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |besselK ν x| ≤ C * Real.exp (-x)) ∧
    (∃ c : ℝ, 0 < c ∧ Tendsto (fun x => Real.exp (-c * x) * besselI ν x) atTop atTop) := by
  exact ⟨GKP1998P.partA ν hν, GKP1998P.partB ν hν⟩
