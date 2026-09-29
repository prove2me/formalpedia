-- Prove2me | solution 1 for BanditAlgorithm.cesaro_average_forgets_transient
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-01T15:45:31.733884+00:00
-- url     : https://prove2.me/submissions/3d527253-b692-4a84-84be-dcb30fc27ba0

import Definitions.Def_TrackAndStop

/-!
# A Cesàro average forgets a transient at rate `1/n`

If a quantity `N` follows a target sequence `p` to within `C`, and the target is
within `δ` of a value `a` from round `M` on — with no control at all before `M`
beyond a crude bound `B` — then the average `N(n)/n` is within `(C + M·B)/n + δ`
of `a`.

The transient contributes `M·B/n` and nothing more.  Read backwards this is the
statement that a *late* failure of the average forces a *late* failure of the
driving sequence, which is what lets a weighted failure series for the average be
traded for a higher-moment series for the target.

Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence,
COLT 2016, the Cesàro step in the proof of Proposition 13; Lattimore &
Szepesvari, Bandit Algorithms (CUP 2020), Lemma 33.8.
-/

open Finset

theorem solution {p N : ℕ → ℝ} {a C B δ : ℝ} {M : ℕ}
    (hC : ∀ n : ℕ, |N n - ∑ s ∈ Finset.range n, p s| ≤ C)
    (hB : ∀ s : ℕ, |p s - a| ≤ B) (hδ : 0 ≤ δ)
    (htail : ∀ s : ℕ, M ≤ s → |p s - a| ≤ δ)
    {n : ℕ} (hn : 0 < n) :
    |N n / (n : ℝ) - a| ≤ (C + (M : ℝ) * B) / (n : ℝ) + δ := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- the deviation of the accumulated target from `n·a`
  have hsum : |(∑ s ∈ Finset.range n, p s) - (n : ℝ) * a| ≤ (M : ℝ) * B + (n : ℝ) * δ := by
    have hrw : (∑ s ∈ Finset.range n, p s) - (n : ℝ) * a
        = ∑ s ∈ Finset.range n, (p s - a) := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.card_range, mul_comm]
    rw [hrw]
    -- split at `M`
    have hsplit : ∑ s ∈ Finset.range n, (p s - a)
        = (∑ s ∈ (Finset.range n).filter (fun s ↦ s < M), (p s - a))
          + ∑ s ∈ (Finset.range n).filter (fun s ↦ ¬ s < M), (p s - a) := by
      rw [Finset.sum_filter_add_sum_filter_not]
    rw [hsplit]
    refine le_trans (abs_add_le _ _) ?_
    have hlow : |∑ s ∈ (Finset.range n).filter (fun s ↦ s < M), (p s - a)| ≤ (M : ℝ) * B := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _ B fun s _ ↦ hB s) ?_
      rw [nsmul_eq_mul]
      have hcard : (((Finset.range n).filter (fun s ↦ s < M)).card : ℝ) ≤ (M : ℝ) := by
        have hsub : ((Finset.range n).filter (fun s ↦ s < M)) ⊆ Finset.range M := by
          intro s hs
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hs).2
        have := Finset.card_le_card hsub
        rw [Finset.card_range] at this
        exact_mod_cast this
      have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
      exact mul_le_mul_of_nonneg_right hcard hB0
    have hhigh : |∑ s ∈ (Finset.range n).filter (fun s ↦ ¬ s < M), (p s - a)| ≤ (n : ℝ) * δ := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _ δ fun s hs ↦ ?_) ?_
      · exact htail s (Nat.not_lt.mp (Finset.mem_filter.mp hs).2)
      · rw [nsmul_eq_mul]
        have hcard : (((Finset.range n).filter (fun s ↦ ¬ s < M)).card : ℝ) ≤ (n : ℝ) := by
          have := Finset.card_le_card (Finset.filter_subset (fun s ↦ ¬ s < M)
            (Finset.range n))
          rw [Finset.card_range] at this
          exact_mod_cast this
        exact mul_le_mul_of_nonneg_right hcard hδ
    linarith
  -- combine with the tracking bound
  have hkey : |N n - (n : ℝ) * a| ≤ C + ((M : ℝ) * B + (n : ℝ) * δ) := by
    have hdecomp : N n - (n : ℝ) * a
        = (N n - ∑ s ∈ Finset.range n, p s)
          + ((∑ s ∈ Finset.range n, p s) - (n : ℝ) * a) := by ring
    rw [hdecomp]
    exact le_trans (abs_add_le _ _) (add_le_add (hC n) hsum)
  -- divide
  have hdiv : |N n / (n : ℝ) - a| = |N n - (n : ℝ) * a| / (n : ℝ) := by
    have hrw : N n / (n : ℝ) - a = (N n - (n : ℝ) * a) / (n : ℝ) := by field_simp
    rw [hrw, abs_div, abs_of_pos hnR]
  rw [hdiv, div_le_iff₀ hnR]
  have : ((C + (M : ℝ) * B) / (n : ℝ) + δ) * (n : ℝ)
      = (C + (M : ℝ) * B) + δ * (n : ℝ) := by field_simp
  rw [this]
  linarith
