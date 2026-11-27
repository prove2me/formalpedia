-- Prove2me | solution 1 for GRH.riemannHypothesis_iff_modulus_one_centered_moebius_bound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T23:58:37.024506+00:00
-- url     : https://prove2.me/submissions/4965aba3-5ab0-4358-a9d3-9fc0714c6c2a

import Theorems.Thm_GRH_riemannHypothesis_iff_upper_mertens_at_squares
import Theorems.Thm_GRH_centered_moebius_bound_iff_square_mertens_residual
import Theorems.Thm_GRH_centered_moebius_bound_iff_square_residue_bias_of_riemannHypothesis
import Mathlib.Tactic.Linarith

open Finset GRH.OneSidedMoebius

private theorem ordinaryResidue (n : ℕ) : residue (1 : ZMod 1) n = mertens n := by
  unfold residue mertens
  have he : range (n+1) = insert 0 (Icc 1 n) := by ext k;simp;omega
  have h (k : ℕ) : (k : ZMod 1) = 1 := Subsingleton.elim _ _
  simp_rw [if_pos (h _)]
  rw [he,sum_insert (by simp)]
  simp

theorem solution : RiemannHypothesis ↔
    ∀ σ : ℝ, (1/2:ℝ) < σ → σ < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear 1 1 N| ≤ C*((N:ℝ)+1)^σ := by
  constructor
  · intro hRH σ hhalf hone
    apply (GRH.centered_moebius_bound_iff_square_residue_bias_of_riemannHypothesis
      hRH 1 1 isUnit_one σ hhalf hone).2
    exact Or.inl (by decide)
  · intro centered
    apply GRH.riemannHypothesis_iff_upper_mertens_at_squares.mpr
    intro σ hhalf hone
    obtain ⟨C,hC,hs⟩ := (GRH.centered_moebius_bound_iff_square_mertens_residual
      1 1 σ hhalf.le).mp (centered σ hhalf hone)
    refine ⟨C,hC,fun u => ?_⟩
    have h := (le_abs_self _).trans (hs u)
    change residue (1 : ZMod 1) (u^2) + _ ≤ _ at h
    rw [ordinaryResidue] at h
    exact (le_add_of_nonneg_right (by positivity)).trans h
