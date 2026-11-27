-- Prove2me | solution 1 for GRH.dirichlet_nonvanishing_of_one_sided_moebius_class_bounds
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:45:32.033296+00:00
-- url     : https://prove2.me/submissions/609948a3-adf6-4e1c-90f5-ffc516980b10

import Definitions.Def_GRH_FactorialMoebius
import Theorems.Thm_GRH_one_sided_moebius_square_cutoffs_iff_all_cutoffs
import Theorems.Thm_GRH_reduced_moebius_principal_bounds_of_dirichlet_prefixes
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_moebius_bound
import Theorems.Thm_dirichlet_mellin_analytic_limit_of_partial_sum_bound
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Finset Filter Topology Asymptotics GRH.OneSidedMoebius GRH.FactorialMoebius

private noncomputable def units (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  univ.filter fun a => IsUnit a

private theorem partition {q : ℕ} [NeZero q] (n : ℕ) :
    ∑ b ∈ units q, residue b n =
      ∑ k ∈ range (n+1), if IsUnit (k:ZMod q) then (ArithmeticFunction.moebius k:ℝ) else 0 := by
  classical
  unfold residue
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  by_cases hk : IsUnit (k:ZMod q)
  · rw [if_pos hk,sum_eq_single (k:ZMod q)]
    · simp
    · intro b _ hb; exact if_neg (Ne.symm hb)
    · intro h; exact (h (mem_filter.mpr ⟨mem_univ _,hk⟩)).elim
  · rw [if_neg hk]
    apply sum_eq_zero
    intro b hb
    apply if_neg
    intro e
    exact hk (e ▸ (mem_filter.mp hb).2)

private theorem principalBound (hRH : RiemannHypothesis) (q : ℕ) [NeZero q] (θ : ℝ)
    (hl : 1/2 < θ) (hr : θ < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, |∑ a ∈ units q, residue a n| ≤ B * ((n:ℝ)+1)^θ := by
  obtain ⟨L,hL⟩ := moebius_dirichlet_partialSum_tendsto_of_moebius_bound θ hl
    (moebius_summatory_rpow_bound_of_riemannHypothesis hRH)
  let f := fun j : ℕ => (ArithmeticFunction.moebius j:ℝ)*(j:ℝ)^(-θ)
  obtain ⟨B,hB⟩ := (Metric.isBounded_range_of_tendsto _ hL.abs).bddAbove
  have hp (n : ℕ) : |∑ j ∈ range n, f j| ≤ max 0 B := by
    cases n with
    | zero => simp
    | succ n =>
      have he : range (n+1) = insert 0 (Icc 1 n) := by ext k; simp; omega
      rw [he,sum_insert (by simp),show f 0=0 by simp [f],zero_add]
      exact (hB ⟨n,rfl⟩).trans (le_max_right ..)
  obtain ⟨K,hK,_,hk⟩ := GRH.reduced_moebius_principal_bounds_of_dirichlet_prefixes q θ
    (max 0 B) hl hr (le_max_left ..) hp
  exact ⟨3*K,by positivity,fun n => by rw [partition]; exact hk n⟩

private theorem residueBound (hRH : RiemannHypothesis) (q : ℕ) [NeZero q] (θ : ℝ)
    (hl : 1/2 < θ) (hr : θ < 1) (h : upper q θ) (a : ZMod q) (ha : IsUnit a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, |residue a n| ≤ D*((n:ℝ)+1)^θ := by
  classical
  obtain ⟨B,hB,hP⟩ := principalBound hRH q θ hl hr
  have each (b : ZMod q) : ∃ C : ℝ, 0 ≤ C ∧
      (IsUnit b → ∀ n : ℕ, residue b n ≤ C*((n:ℝ)+1)^θ) := by
    by_cases hb : IsUnit b
    · obtain ⟨C,hC,hb'⟩ := (GRH.one_sided_moebius_square_cutoffs_iff_all_cutoffs b θ hl.le).1 (h b hb)
      exact ⟨C,hC,fun _ => hb'⟩
    · exact ⟨0,le_rfl,fun h => (hb h).elim⟩
  choose C hC hU using each
  let D := ∑ b ∈ units q,C b
  have hD : 0 ≤ D := sum_nonneg fun b _ => hC b
  have ha' : a ∈ units q := mem_filter.mpr ⟨mem_univ _,ha⟩
  refine ⟨C a+D+B,add_nonneg (add_nonneg (hC a) hD) hB,fun n => ?_⟩
  let X := ((n:ℝ)+1)^θ
  have hx : 0 ≤ X := Real.rpow_nonneg (by positivity) _
  have other : ∑ b ∈ (units q).erase a,residue b n ≤ D*X := by
    calc
      _ ≤ ∑ b ∈ (units q).erase a,C b*X := sum_le_sum fun b hb =>
        hU b (mem_filter.mp (mem_of_mem_erase hb)).2 n
      _ = (∑ b ∈ (units q).erase a,C b)*X := (sum_mul ..).symm
      _ ≤ D*X := by
        apply mul_le_mul_of_nonneg_right _ hx
        dsimp only [D]
        rw [← sum_erase_add (units q) C ha']
        exact le_add_of_nonneg_right (hC a)
  have mass := sum_erase_add (units q) (fun b => residue b n) ha'
  have lower := (abs_le.mp (hP n)).1
  change |residue a n| ≤ (C a+D+B)*X
  apply abs_le.mpr
  constructor
  · nlinarith only [lower,other,mass,mul_nonneg (hC a) hx]
  · nlinarith only [hU a ha n,mul_nonneg hD hx,mul_nonneg hB hx]

private theorem twistedNonzero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    {θ : ℝ} (hθ : 0 ≤ θ) (h1 : θ < 1)
    (hO : (fun n : ℕ => ∑ k ∈ range (n+1), χ k*(ArithmeticFunction.moebius k:ℂ))
      =O[atTop] (fun n : ℕ => (n:ℝ)^θ)) :
    ∀ s : ℂ, θ < s.re → χ.LFunction s ≠ 0 := by
  let f : ℕ → ℂ := fun k => χ k*(ArithmeticFunction.moebius k:ℂ)
  have ranges (n : ℕ) : range (n+1) = insert 0 (Icc 1 n) := by ext k; simp; omega
  have same (n : ℕ) : ∑ k ∈ range (n+1), f k = ∑ k ∈ Icc 1 n,f k := by
    rw [ranges,sum_insert (by simp)]
    simp [f]
  change (fun n : ℕ => ∑ k ∈ range (n+1), f k) =O[atTop] _ at hO
  simp_rw [same] at hO
  let F := fun s : ℂ => s * mellin (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, f k) (-s)
  obtain ⟨ha,hlim⟩ := dirichlet_mellin_analytic_limit_of_partial_sum_bound f hθ hO
  let V := {s : ℂ | θ < s.re}
  have hV : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hA : AnalyticOnNhd ℂ (fun z => χ.LFunction z * F z) V :=
    ((χ.differentiable_LFunction hn).differentiableOn.analyticOnNhd hV).mul ha
  have h2 : (2:ℂ) ∈ V := by change θ < (2:ℂ).re; norm_num; linarith
  have eq : Set.EqOn (fun z => χ.LFunction z * F z) (fun _ => 1) V := by
    apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hA analyticOnNhd_const
      (convex_halfSpace_re_gt θ).isPreconnected h2
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1:ℝ) < (2:ℂ).re by norm_num)] with s hs
    have summable : LSeriesSummable f s :=
      DirichletCharacter.LSeriesSummable_mul χ (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
    have conv := (tendsto_add_atTop_iff_nat 1).mpr summable.hasSum.tendsto_sum_nat
    have es (n : ℕ) : ∑ k ∈ range (n+1), LSeries.term f s k =
        ∑ k ∈ Icc 1 n, f k / (k:ℂ)^s := by
      rw [ranges,sum_insert (by simp),LSeries.term_zero,zero_add]
      exact sum_congr rfl fun k hk => LSeries.term_of_ne_zero (Nat.ne_of_gt (mem_Icc.mp hk).1) ..
    simp_rw [es] at conv
    have he : F s = LSeries f s := tendsto_nhds_unique (hlim s (h1.trans hs)) conv
    change χ.LFunction s * F s = 1
    rw [he,χ.LFunction_eq_LSeries hs]
    exact DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  intro s hs hz
  have e := eq (show s ∈ V from hs)
  change χ.LFunction s * F s = 1 at e
  simp [hz] at e

theorem solution (hRH : RiemannHypothesis) (q : ℕ) [NeZero q] (θ : ℝ)
    (hl : 1/2 < θ) (hr : θ < 1) (h : upper q θ) :
    ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), θ < s.re → ¬ (χ=1 ∧ s=1) → χ.LFunction s ≠ 0 := by
  classical
  intro χ s hs hp
  by_cases high : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hp) high
  have low := lt_of_not_ge high
  by_cases hn : χ=1
  · subst χ
    have hs1 : s ≠ 1 := fun e => hp ⟨rfl,e⟩
    change DirichletCharacter.LFunctionTrivChar q s ≠ 0
    rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1]
    apply mul_ne_zero (prod_ne_zero_iff.mpr ?_) ?_
    · intro p hprime
      have pr := Nat.prime_of_mem_primeFactors hprime
      have small : ‖(p:ℂ)^(-s)‖ < 1 := by
        rw [Complex.norm_natCast_cpow_of_pos pr.pos,Complex.neg_re]
        exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast pr.one_lt) (by linarith)
      intro e
      rw [← sub_eq_zero.mp e,norm_one] at small
      exact lt_irrefl _ small
    · intro hz
      have e := riemannHypothesis_iff_zeros_in_strip_on_line.mp hRH s hz (by linarith) low
      linarith
  apply twistedNonzero χ hn (by linarith) hr _ s hs
  have each (a : ZMod q) : ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ,
      ‖χ a * (residue a n : ℂ)‖ ≤ D*((n:ℝ)+1)^θ := by
    by_cases ha : IsUnit a
    · obtain ⟨D,hD,hd⟩ := residueBound hRH q θ hl hr h a ha
      refine ⟨D,hD,fun n => ?_⟩
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (abs_nonneg _) (χ.norm_le_one _)).trans (hd n)
    · exact ⟨0,le_rfl,fun n => by simp [χ.map_nonunit ha]⟩
  choose C hC hbound using each
  let B := ∑ a, C a
  have hB : 0 ≤ B := sum_nonneg fun a _ => hC a
  have grouped (n : ℕ) : ∑ k ∈ range (n+1), χ k*(ArithmeticFunction.moebius k:ℂ) =
      ∑ a : ZMod q, χ a*(residue a n:ℂ) := by
    simp only [residue,Complex.ofReal_sum,mul_sum]
    rw [sum_comm (s := (univ : Finset (ZMod q)))]
    apply sum_congr rfl
    intro k _
    simp [apply_ite Complex.ofReal,mul_ite]
  refine Asymptotics.IsBigO.of_bound (B*2^θ) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [grouped,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  have scale := Real.rpow_le_rpow (show 0 ≤ (n:ℝ)+1 by positivity)
    (show (n:ℝ)+1 ≤ 2*(n:ℝ) by linarith) (show 0 ≤ θ by linarith)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg n)] at scale
  calc
    _ ≤ ∑ a : ZMod q, ‖χ a * (residue a n:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ a : ZMod q, C a*((n:ℝ)+1)^θ := sum_le_sum fun a _ => hbound a n
    _ = B*((n:ℝ)+1)^θ := (sum_mul ..).symm
    _ ≤ B*2^θ*(n:ℝ)^θ := (mul_le_mul_of_nonneg_left scale hB).trans_eq (by ring)
