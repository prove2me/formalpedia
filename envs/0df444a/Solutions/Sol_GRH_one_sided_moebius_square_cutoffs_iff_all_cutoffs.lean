-- Prove2me | solution 1 for GRH.one_sided_moebius_square_cutoffs_iff_all_cutoffs
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T20:55:45.810419+00:00
-- url     : https://prove2.me/submissions/02054a98-1b43-48ec-aad3-6c7c9d084ecb

import Definitions.Def_GRH_OneSidedMoebius
import Mathlib.Tactic.Linarith

open Finset GRH.OneSidedMoebius

private theorem increment {q : ℕ} (a : ZMod q) (s j : ℕ) :
    residue a (s+j) - residue a s ≤ (j : ℝ) := by
  unfold residue
  rw [show s+j+1=s+1+j by omega, sum_range_add, add_sub_cancel_left]
  calc
    _ ≤ ∑ _k ∈ range j, (1 : ℝ) := by
      apply sum_le_sum
      intro k _
      split_ifs
      · exact_mod_cast (le_abs_self _).trans (ArithmeticFunction.abs_moebius_le_one (n := s+1+k))
      · norm_num
    _ = _ := by simp

theorem solution {q : ℕ} (a : ZMod q) (σ : ℝ) (hσ : (1/2 : ℝ) ≤ σ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ, residue a (u^2) ≤ C*((u:ℝ)^2+1)^σ) ↔
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, residue a N ≤ D*((N:ℝ)+1)^σ := by
  constructor
  · rintro ⟨C,hC,H⟩
    refine ⟨C+2,by positivity,fun N => ?_⟩
    let u := N.sqrt
    have hs : u^2 ≤ N := Nat.sqrt_le' N
    have hsr : (u : ℝ)^2 ≤ N := by exact_mod_cast hs
    have hgap : N-u^2 ≤ 2*u := by
      have h : N ≤ u^2+2*u := by simpa [u,pow_two,two_mul,add_assoc] using Nat.sqrt_le_add N
      omega
    have hi := increment a (u^2) (N-u^2)
    rw [Nat.add_sub_of_le hs] at hi
    have hj : ((N-u^2 : ℕ) : ℝ) ≤ 2*(u:ℝ) := by exact_mod_cast hgap
    have hu : (u:ℝ) ≤ ((N:ℝ)+1)^σ := by
      calc
        _ ≤ Real.sqrt ((N:ℝ)+1) := (Real.le_sqrt (by positivity) (by positivity)).mpr (by linarith)
        _ ≤ _ := by rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le (by simp) hσ
    have hscale := Real.rpow_le_rpow (show 0 ≤ (u:ℝ)^2+1 by positivity)
      (show (u:ℝ)^2+1 ≤ (N:ℝ)+1 by linarith) (show 0≤σ by linarith)
    have hm := (H u).trans (mul_le_mul_of_nonneg_left hscale hC)
    linarith only [hi,hj,hu,hm]
  · rintro ⟨D,hD,H⟩
    refine ⟨D,hD,fun u => ?_⟩
    have h := H (u*u)
    rw [Nat.cast_mul] at h
    simpa only [pow_two] using h
