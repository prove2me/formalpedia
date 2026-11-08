-- Prove2me | solution 1 for CompetitionComplexity.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:58:08.885078+00:00
-- url     : https://prove2.me/submissions/6da097ac-88af-4c4a-b6ec-6d6f60815ab2

import Mathlib
import Definitions.Def_CompetitionComplexity_SequenceProperties

open Filter Topology

open CompetitionComplexity in
theorem solution (B : ℕ → ℝ) (hB0 : B 0 = 0) (ha : CompetitionComplexity.PropA B)
    (hb : CompetitionComplexity.PropB B) (hc : CompetitionComplexity.PropC B)
    (ρ : ℝ) (hρ : Tendsto (fun n => CompetitionComplexity.dS B (n + 1) / CompetitionComplexity.dS B n)
      atTop (𝓝 ρ)) (hρ1 : ρ < 1) :
    ∃ Bv : ℝ, 0 < Bv ∧ Tendsto B atTop (𝓝 Bv) := by
  have hd : ∀ n, 0 < CompetitionComplexity.dS B n := fun n => by
    unfold CompetitionComplexity.dS
    exact sub_pos.2 (ha (Nat.lt_succ_self n))
  have hr : ∀ n, CompetitionComplexity.dS B (n + 1) / CompetitionComplexity.dS B n ≤ ρ :=
    fun n => Monotone.ge_of_tendsto hc hρ n
  have hρ0 : 0 ≤ ρ := (div_pos (hd 1) (hd 0)).le.trans (hr 0)
  have hgeo : ∀ n, CompetitionComplexity.dS B n ≤ CompetitionComplexity.dS B 0 * ρ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := hr n
      rw [div_le_iff₀ (hd n)] at h1
      calc CompetitionComplexity.dS B (n + 1) ≤ ρ * CompetitionComplexity.dS B n := h1
        _ ≤ ρ * (CompetitionComplexity.dS B 0 * ρ ^ n) := mul_le_mul_of_nonneg_left ih hρ0
        _ = CompetitionComplexity.dS B 0 * ρ ^ (n + 1) := by ring
  have hsum : ∀ n, B n = ∑ m ∈ Finset.range n, CompetitionComplexity.dS B m := by
    intro n
    induction n with
    | zero => simp [hB0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      unfold CompetitionComplexity.dS
      ring
  have hbound : ∀ n, B n ≤ CompetitionComplexity.dS B 0 / (1 - ρ) := by
    intro n
    have h1 : ∑ m ∈ Finset.range n, CompetitionComplexity.dS B m ≤
        CompetitionComplexity.dS B 0 * ∑ m ∈ Finset.range n, ρ ^ m := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun m _ => hgeo m)
    have h2 : (1 - ρ) * ∑ m ∈ Finset.range n, ρ ^ m ≤ 1 := by
      rw [mul_neg_geom_sum]
      have := pow_nonneg hρ0 n
      linarith
    have h3 : ∑ m ∈ Finset.range n, ρ ^ m ≤ 1 / (1 - ρ) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    rw [hsum n, div_eq_mul_one_div]
    exact h1.trans (mul_le_mul_of_nonneg_left h3 (hd 0).le)
  have hbdd : BddAbove (Set.range B) := ⟨_, by rintro _ ⟨n, rfl⟩; exact hbound n⟩
  refine ⟨⨆ n, B n, ?_, tendsto_atTop_ciSup ha.monotone hbdd⟩
  have hB1 : B 1 = CompetitionComplexity.dS B 0 := by
    unfold CompetitionComplexity.dS; rw [hB0]; ring
  have := le_ciSup hbdd 1
  rw [hB1] at this
  linarith [hd 0]
