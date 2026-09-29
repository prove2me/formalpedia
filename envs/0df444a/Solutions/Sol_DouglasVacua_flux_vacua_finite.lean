-- Prove2me | solution 1 for DouglasVacua.flux_vacua_finite
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T04:23:14.773158+00:00
-- url     : https://prove2.me/submissions/448e28f9-6d68-4370-8c62-13344dfa3180

import Mathlib
import Definitions.Def_douglas_flux_vacua_count

set_option autoImplicit false

open DouglasVacua in
theorem solution (J : ℕ) (c : ℝ) (hc : 0 < c) (V : ℝ) :
    Set.Finite {N : Fin J → ℤ | fluxPotential c N ≤ V} := by
  set B : ℤ := ⌈V / c⌉ with hB
  refine (Set.Finite.pi (t := fun _ : Fin J => Set.Icc (-B) B)
    (fun _ => Set.finite_Icc (-B) B)).subset ?_
  intro N hN
  simp only [Set.mem_ofPred_eq, fluxPotential] at hN
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  intro i
  have hsum : ((N i : ℝ)) ^ 2 ≤ ∑ j, ((N j : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun j => ((N j : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hle : ((N i : ℝ)) ^ 2 ≤ V / c := by
    rw [le_div_iff₀ hc]
    nlinarith
  have habs : (|N i| : ℤ) ≤ N i ^ 2 := by
    rw [← sq_abs (N i)]
    rcases (abs_nonneg (N i)).eq_or_lt with h | h
    · rw [← h]; norm_num
    · nlinarith
  have habsR : ((|N i| : ℤ) : ℝ) ≤ V / c := by
    have : ((|N i| : ℤ) : ℝ) ≤ ((N i : ℝ)) ^ 2 := by exact_mod_cast habs
    linarith
  have hceil : |N i| ≤ B := by
    rw [hB]
    exact_mod_cast habsR.trans (Int.le_ceil (V / c))
  exact abs_le.mp hceil
