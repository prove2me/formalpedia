-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_uniform_large_cells_cross_finite_true_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:03:20.21376+00:00
-- url     : https://prove2.me/submissions/c6d3449e-d8ca-4b7f-9f74-87d807a3f6e8

import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_large_shrinking_cells_pinpoint_true_jump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Every sufficiently fine source-grid cell with a large increment must
cross a genuine jump in the prescribed finite large-jump set. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (a b : ℕ → ℕ → ℝ≥0) (w : ℕ → ℝ≥0)
    (haT : ∀ n i, a n i ≤ T)
    (hab : ∀ n i, a n i ≤ b n i)
    (hbw : ∀ n i, b n i ≤ a n i + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0)))
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (F : Finset ℝ≥0)
    (hF : ∀ t ∈ Icc (0 : ℝ≥0) T,
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F) :
    ∀ᶠ n in (atTop : Filter ℕ), ∀ i,
      ρ ≤ |Y (b n i) - Y (a n i)| →
      ∃ t ∈ F, a n i < t ∧ t ≤ b n i := by
  classical
  by_contra hnot
  have hfreq : ∃ᶠ n in (atTop : Filter ℕ),
      ¬∀ i, ρ ≤ |Y (b n i) - Y (a n i)| →
        ∃ t ∈ F, a n i < t ∧ t ≤ b n i :=
    (Filter.not_eventually).mp hnot
  have hbad : ∃ᶠ n in (atTop : Filter ℕ),
      ∃ i, ρ ≤ |Y (b n i) - Y (a n i)| ∧
        (∀ t ∈ F, ¬(a n i < t ∧ t ≤ b n i)) := by
    refine hfreq.mono ?_
    intro n hn
    push_neg at hn
    obtain ⟨i, hi, havoid⟩ := hn
    refine ⟨i, hi, ?_⟩
    intro t ht ⟨hat, htb⟩
    exact (not_lt_of_ge htb) (havoid t ht hat)
  obtain ⟨φ, hφ, hbadφ⟩ :=
    Filter.exists_seq_forall_of_frequently hbad
  let j : ℕ → ℕ := fun n => Classical.choose (hbadφ n)
  have hspec : ∀ n,
      ρ ≤ |Y (b (φ n) (j n)) - Y (a (φ n) (j n))| ∧
      ∀ t ∈ F, ¬(a (φ n) (j n) < t ∧ t ≤ b (φ n) (j n)) :=
    fun n => Classical.choose_spec (hbadφ n)
  obtain ⟨t, ht, hjump, ψ, _hψ, hcross⟩ :=
    avram_p2_a_zero_rate_large_shrinking_cells_pinpoint_true_jump
      Y T (fun n => a (φ n) (j n)) (fun n => b (φ n) (j n))
      (fun n => w (φ n)) (fun n => haT (φ n) (j n))
      (fun n => hab (φ n) (j n))
      (fun n => hbw (φ n) (j n))
      (hw.comp hφ) hL hR ρ hρ (fun n => (hspec n).1)
  exact ((hspec (ψ 0)).2 t (hF t ht hjump)) (hcross 0)
