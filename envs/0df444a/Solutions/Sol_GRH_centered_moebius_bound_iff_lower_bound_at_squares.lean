-- Prove2me | solution 1 for GRH.centered_moebius_bound_iff_lower_bound_at_squares
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T20:58:37.531422+00:00
-- url     : https://prove2.me/submissions/b0e60c6e-a9bb-47e9-9658-694957582af4

import Theorems.Thm_GRH_centered_moebius_iff_one_sided_residue_squares
import Theorems.Thm_GRH_centered_moebius_mertens_remainder
import Mathlib.Tactic.Linarith

open GRH.OneSidedMoebius

theorem solution : centeredBound ↔
    ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a → ∀ σ : ℝ, 1/2 < σ → σ < 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ,
        -(C*((u:ℝ)^2+1)^σ) ≤ GRH.centeredMoebiusBilinear q a (u^2) := by
  constructor
  · intro H q _ a ha σ hσ h₁
    obtain ⟨C,hC,h⟩ := H q a ha σ hσ h₁
    refine ⟨C,hC,fun u => ?_⟩
    have hb := (abs_le.mp (h (u*u))).1
    rw [Nat.cast_mul] at hb
    simpa only [pow_two] using hb
  · intro H
    apply GRH.centered_moebius_iff_one_sided_residue_squares.mpr
    intro q _ a ha σ hσ h₁
    obtain ⟨C,hC,h⟩ := H q a ha σ hσ h₁
    refine ⟨C+2,by positivity,fun u => ?_⟩
    have rem := (GRH.centered_moebius_mertens_remainder q a (u^2)).2
    dsimp only at rem
    rw [Nat.sqrt_eq' u,Nat.cast_pow] at rem
    have hu : (u:ℝ) ≤ ((u:ℝ)^2+1)^σ := by
      calc
        _ ≤ Real.sqrt ((u:ℝ)^2+1) := (Real.le_sqrt (by positivity) (by positivity)).mpr (by linarith)
        _ ≤ _ := by rw [Real.sqrt_eq_rpow];exact Real.rpow_le_rpow_of_exponent_le (by simp) hσ.le
    have ht : 0 ≤ 1/(q:ℝ)*(u:ℝ)^2*(GRH.reducedMoebiusHarmonic q u)^2 := by positivity
    have hr := (le_abs_self _).trans rem
    change GRH.centeredMoebiusBilinear q a (u^2) + (residue a (u^2)+_) ≤ _ at hr
    linarith only [hr,ht,hu,h u]
