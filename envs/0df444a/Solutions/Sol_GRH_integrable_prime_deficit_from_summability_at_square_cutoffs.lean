-- Prove2me | solution 1 for GRH.integrable_prime_deficit_from_summability_at_square_cutoffs
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T02:22:16.569096+00:00
-- url     : https://prove2.me/submissions/c42e3863-c387-4875-9bab-2b01388e6df3

import Definitions.Def_GRH_PrimeDeficitMean
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter GRH.SplitPrimeLower GRH.PrimeDeficitMean

private theorem prime_mono (q : ℕ) : Monotone (primeWeight q) := by
  intro m n h
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h)
  intro i _ _
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.1.one_le)
  · rfl

private theorem meas (q : ℕ) : Measurable (deficit q) :=
  (measurable_id.sub (measurable_const.mul ((measurable_of_countable (primeWeight q)).comp
    Nat.measurable_floor))).max measurable_const

theorem solution (q : ℕ) (θ : ℝ) (hθ : 1/2<θ) (h : squareMean q θ) :
    IntegrableOn (fun x : ℝ => deficit q x * x^(-θ-1)) (Ioi 1) := by
  let u := fun n : ℕ => ((n+1:ℕ):ℝ)
  let I := fun n : ℕ => Icc ((u n)^2) ((u n+1)^2)
  let F := fun x : ℝ => deficit q x * x^(-θ-1)
  let B := fun n : ℕ => (deficit q ((u n)^2)+3*u n)*(u n)^(-2*θ-2)
  have hu (n : ℕ) : 1≤u n := by dsimp only [u];exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hp (n : ℕ) : 0<u n := zero_lt_one.trans_le (hu n)
  have hD (x : ℝ) : 0≤deficit q x := le_max_right .. 
  have hB (n : ℕ) : 0≤B n := by dsimp only [B];positivity [hD ((u n)^2),hp n]
  have hm : Measurable F := (meas q).mul (measurable_id.pow_const _)
  have bound (n : ℕ) (x : ℝ) (hx : x ∈ I n) : ‖F x‖ ≤ B n := by
    have hx0 : 0<x := (sq_pos_of_pos (hp n)).trans_le hx.1
    have hstep : deficit q x ≤ deficit q ((u n)^2)+3*u n := by
      apply max_le
      · have hc := mul_le_mul_of_nonneg_left (prime_mono q (Nat.floor_mono hx.1))
          (Nat.cast_nonneg (α:=ℝ) q.totient)
        have hj : (u n)^2-(q.totient:ℝ)*primeWeight q ⌊(u n)^2⌋₊ ≤ deficit q ((u n)^2) := le_max_left .. 
        nlinarith only [hc,hj,hx.2,hu n]
      · positivity [hD ((u n)^2),hp n]
    have hr := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (hp n)) hx.1
      (show -θ-1≤0 by linarith)
    rw [← Real.rpow_natCast (u n) 2,← Real.rpow_mul (hp n).le] at hr
    have he : (2:ℝ)*(-θ-1) = -2*θ-2 := by ring
    norm_num only [Nat.cast_ofNat] at hr
    rw [he] at hr
    change ‖deficit q x * x^(-θ-1)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hD x) (Real.rpow_nonneg hx0.le _))]
    exact mul_le_mul hstep hr (Real.rpow_nonneg hx0.le _) (by positivity [hD ((u n)^2),hp n])
  have hi (n : ℕ) : IntegrableOn F (I n) := by
    have hc : IntegrableOn (fun _ : ℝ => B n) (I n) :=
      integrableOn_const (by simp [I])
    exact hc.mono' hm.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Icc).mono fun x hx => bound n x hx)
  have hs : Summable (fun n : ℕ => (u n)^(-2*θ)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))
  have he1 (n : ℕ) : (u n)^(-2*θ-1) = u n*(u n)^(-2*θ-2) := by
    rw [show -2*θ-1 = 1+(-2*θ-2) by ring,Real.rpow_add (hp n),Real.rpow_one]
  have he2 (n : ℕ) : (u n)^(-2*θ) = u n*(u n)^(-2*θ-1) := by
    calc
      _ = (u n)^(1+(-2*θ-1)) := by congr 1;ring
      _ = _ := by rw [Real.rpow_add (hp n),Real.rpow_one]
  have sums : Summable (fun n : ℕ => ∫ x in I n, ‖F x‖) := by
    refine Summable.of_nonneg_of_le (f:=fun n : ℕ => 3*deficitTerm q θ n+9*(u n)^(-2*θ))
      (fun n => integral_nonneg fun x => norm_nonneg (F x)) ?_ ((h.mul_left 3).add (hs.mul_left 9))
    intro n
    have hc : IntegrableOn (fun _ : ℝ => B n) (I n) := integrableOn_const (by simp [I])
    have ha : (u n)^2 ≤ (u n+1)^2 := by nlinarith [hp n]
    calc
      _ ≤ ∫ _ in I n, B n := setIntegral_mono_on (hi n).norm hc measurableSet_Icc (bound n)
      _ = ((u n+1)^2-(u n)^2)*B n := by rw [setIntegral_const,Real.volume_real_Icc_of_le ha,smul_eq_mul]
      _ ≤ (3*u n)*B n := mul_le_mul_of_nonneg_right (by nlinarith only [hu n]) (hB n)
      _ = _ := by
        change _ = 3*(deficit q ((u n)^2)*(u n)^(-2*θ-1)) + 9*(u n)^(-2*θ)
        rw [he2,he1];dsimp only [B];ring
  apply (integrableOn_iUnion_of_summable_integral_norm hi sums).mono_set
  intro x hx
  have hx1 : 1<x := hx
  have hx0 : 0≤x := by linarith
  let a := ⌊Real.sqrt x⌋₊
  have hs1 : 1≤Real.sqrt x := (Real.le_sqrt (by norm_num) hx0).mpr (by linarith)
  have ha : 1≤a := Nat.le_floor (by exact_mod_cast hs1)
  have hn : u (a-1) = (a:ℝ) := by dsimp only [u];rw [Nat.sub_add_cancel ha]
  refine mem_iUnion.mpr ⟨a-1,?_⟩
  change (u (a-1))^2 ≤ x ∧ x ≤ (u (a-1)+1)^2
  rw [hn,← Real.sq_sqrt hx0]
  exact ⟨pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (Real.sqrt_nonneg _)) 2,
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (Nat.lt_floor_add_one (Real.sqrt x)).le 2⟩
