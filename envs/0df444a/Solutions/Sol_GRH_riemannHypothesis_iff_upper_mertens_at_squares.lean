-- Prove2me | solution 1 for GRH.riemannHypothesis_iff_upper_mertens_at_squares
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T20:57:12.385851+00:00
-- url     : https://prove2.me/submissions/5a0f7439-038c-4e70-99ac-fb2188bbd76f

import Theorems.Thm_GRH_zeta_zero_free_of_one_sided_mertens_bound
import Theorems.Thm_GRH_one_sided_moebius_square_cutoffs_iff_all_cutoffs
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Mathlib.Tactic.Linarith

open Finset Filter GRH.OneSidedMoebius

private theorem ordinaryResidue (n : ℕ) : residue (1 : ZMod 1) n = mertens n := by
  unfold residue mertens
  have he : range (n+1) = insert 0 (Icc 1 n) := by ext k;simp;omega
  simp_rw [Subsingleton.elim (_ : ZMod 1) (1:ZMod 1), if_true]
  rw [he,sum_insert (by simp)]
  simp

private theorem mertens_abs (n : ℕ) : |mertens n| ≤ n := by
  calc
    _ ≤ ∑ k ∈ Icc 1 n, |(ArithmeticFunction.moebius k : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Icc 1 n, (1:ℝ) := sum_le_sum fun k _ => by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=k)
    _ = _ := by simp

theorem solution : RiemannHypothesis ↔
    ∀ θ : ℝ, 1/2 < θ → θ < 1 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ℕ, mertens (u^2) ≤ C*((u:ℝ)^2+1)^θ := by
  constructor
  · intro hRH θ hθ _
    obtain ⟨C,hC,H⟩ := (moebius_summatory_rpow_bound_of_riemannHypothesis hRH
      (θ-1/2) (by linarith)).exists_nonneg
    obtain ⟨n₀,hn⟩ := eventually_atTop.mp H.bound
    have hθ0 : 0 ≤ θ := by linarith
    have hpow (u : ℕ) : (1:ℝ) ≤ ((u:ℝ)^2+1)^θ :=
      Real.one_le_rpow (by nlinarith only [sq_nonneg (u:ℝ)]) hθ0
    refine ⟨C+n₀,by positivity,fun u => ?_⟩
    by_cases hu : n₀ ≤ u^2
    · have h := hn (u^2) hu
      have he (n : ℕ) : (mertens n:ℂ) = ∑ k ∈ Icc 1 n, (ArithmeticFunction.moebius k : ℂ) := by
        unfold mertens;push_cast;rfl
      rw [← he,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at h
      rw [show 1/2+(θ-1/2)=θ by ring,Nat.cast_pow] at h
      have hp := Real.rpow_le_rpow (sq_nonneg (u:ℝ))
        (show (u:ℝ)^2≤(u:ℝ)^2+1 by linarith) hθ0
      nlinarith only [le_abs_self (mertens (u^2)), h, mul_le_mul_of_nonneg_left hp hC,
        mul_nonneg (Nat.cast_nonneg (α:=ℝ) n₀) (zero_le_one.trans (hpow u))]
    · have h := (le_abs_self _).trans (mertens_abs (u^2))
      have ht : (((u^2:ℕ):ℝ)) ≤ n₀ := by exact_mod_cast (lt_of_not_ge hu).le
      have hp := mul_le_mul_of_nonneg_left (hpow u) (Nat.cast_nonneg (α:=ℝ) n₀)
      nlinarith only [h,ht,hp,mul_nonneg hC (zero_le_one.trans (hpow u))]
  · intro upper
    have nozero (s : ℂ) (hx : 1/2 < s.re) (hx' : s.re < 1) : riemannZeta s ≠ 0 := by
      let θ := (1/2+s.re)/2
      have ht : 1/2 < θ := by dsimp [θ];linarith
      have hts : θ < s.re := by dsimp [θ];linarith
      have ht1 := hts.trans hx'
      obtain ⟨C,hC,H⟩ := upper θ ht ht1
      obtain ⟨D,hD,HD⟩ := (GRH.one_sided_moebius_square_cutoffs_iff_all_cutoffs
        (1 : ZMod 1) θ ht.le).mp ⟨C,hC,fun u => by rw [ordinaryResidue];exact H u⟩
      exact GRH.zeta_zero_free_of_one_sided_mertens_bound θ (by linarith) ht1 D hD
        (fun n => by rw [← ordinaryResidue];exact HD n) s hts (by intro e;simp [e] at hx')
    apply riemannHypothesis_iff_zeros_in_strip_on_line.2
    intro s hz h₀ h₁
    rcases lt_trichotomy s.re (1/2) with hlt|heq|hgt
    · have hnat (n : ℕ) : s ≠ -n := by
        intro e
        have h := congrArg Complex.re e
        simp at h
        linarith [Nat.cast_nonneg (α:=ℝ) n]
      have hne : s ≠ 1 := by intro e;simp [e] at h₁
      have reflected : riemannZeta (1-s)=0 := by rw [riemannZeta_one_sub hnat hne,hz,mul_zero]
      exact (nozero (1-s) (by simp only [Complex.sub_re,Complex.one_re];linarith)
        (by simp only [Complex.sub_re,Complex.one_re];linarith) reflected).elim
    · exact heq
    · exact (nozero s hgt h₁ hz).elim
