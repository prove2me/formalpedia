-- Prove2me | solution 1 for EulerMascheroni.Sondow.cutoffError_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:55:45.290494+00:00
-- url     : https://prove2.me/submissions/56821675-abd4-4f13-9bfa-e99755151104

import Definitions.Def_eulerMascheroni_sondowCutoff
import Mathlib.Tactic

open Filter Finset EulerMascheroni.Sondow
open scoped Topology

private lemma harmonic_shift_limit (a : ℕ) :
    Tendsto (fun N : ℕ => (harmonic (N+a) : ℝ)-(harmonic N : ℝ)) atTop (𝓝 0) := by
  induction a with
  | zero => simpa using (tendsto_const_nhds (x := (0:ℝ)))
  | succ a ih =>
    have ha : Tendsto (fun N : ℕ => (N:ℝ)+(a+1:ℕ)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hi := tendsto_inv_atTop_zero.comp ha
    convert ih.add hi using 1
    · congr 1; funext N
      rw [Nat.add_succ, harmonic_succ]
      push_cast
      dsimp only [Function.comp_def]
      ring
    · simp

private lemma log_shift_limit (a : ℕ) :
    Tendsto (fun N : ℕ => Real.log (1+(a:ℝ)/(N:ℝ))) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := (tendsto_const_nhds.add (hN.const_mul (a:ℝ))).log (by norm_num : (1:ℝ)+(a:ℝ)*0 ≠ 0)
  simpa [div_eq_mul_inv] using hh

theorem solution (n : ℕ) : Tendsto (cutoffError n) atTop (𝓝 0) := by
  have hdiag : Tendsto (fun N : ℕ =>
      ∑ i ∈ range (n+1), (n.choose i : ℝ)^2 *
        ((harmonic (N+n+i) : ℝ)-(harmonic N : ℝ))) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (range (n+1)) (fun i _ =>
      (harmonic_shift_limit (n+i)).const_mul ((n.choose i : ℝ)^2))
    simpa [Nat.add_assoc] using h
  have hoff : Tendsto (fun N : ℕ =>
      2 * ∑ i ∈ range (n+1), ∑ j ∈ Icc (i+1) n,
        ((-1:ℝ)^(i+j)*(n.choose i : ℝ)*(n.choose j : ℝ)/(j-i:ℕ)) *
          ∑ k ∈ Icc 1 (j-i), Real.log (1+(n+i+k:ℕ)/(N:ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_finsetSum (range (n+1)) (fun i _ =>
      tendsto_finsetSum (Icc (i+1) n) (fun j _ =>
        (tendsto_finsetSum (Icc 1 (j-i)) (fun k _ => log_shift_limit (n+i+k))).const_mul
          ((-1:ℝ)^(i+j)*(n.choose i : ℝ)*(n.choose j : ℝ)/(j-i:ℕ))))).const_mul 2
    simpa using h
  change Tendsto (fun N => cutoffError n N) atTop (𝓝 0)
  simpa [cutoffError] using hdiag.add hoff

#print axioms solution
