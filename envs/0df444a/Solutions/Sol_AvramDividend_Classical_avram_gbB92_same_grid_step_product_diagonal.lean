-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB92_same_grid_step_product_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:38:18.901392+00:00
-- url     : https://prove2.me/submissions/9856f419-7383-4dc4-8ff2-3d8fb5bc16bb

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    (N : ℕ) (δ t : ℝ) (hδ : 0 < δ)
    (H J : ℕ → ℝ) :
    ((Finset.range N).sum (fun r =>
      if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
      then H r else 0)) *
    ((Finset.range N).sum (fun r =>
      if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
      then J r else 0)) =
    (Finset.range N).sum (fun r =>
      if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
      then H r * J r else 0) := by
  let p (r : ℕ) : Prop :=
    (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
  have hunique (r s : ℕ) (hr : p r) (hs : p s) : r = s := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hrs | hsr
    · have hc : ((r + 1 : ℕ) : ℝ) * δ ≤ (s : ℝ) * δ :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.succ_le_of_lt hrs) (le_of_lt hδ)
      exact (not_lt_of_ge (hc.trans hs.1)) hr.2
    · have hc : ((s + 1 : ℕ) : ℝ) * δ ≤ (r : ℝ) * δ :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.succ_le_of_lt hsr) (le_of_lt hδ)
      exact (not_lt_of_ge (hc.trans hr.1)) hs.2
  have hsingle (C : ℕ → ℝ) (r : ℕ)
      (hr : r ∈ Finset.range N) (hp : p r) :
      (Finset.range N).sum (fun s => if p s then C s else 0) = C r := by
    rw [Finset.sum_eq_single r]
    · exact if_pos hp
    · intro s hs hsr
      have hnot : ¬p s := by
        intro hps
        exact hsr (hunique s r hps hp)
      exact if_neg hnot
    · intro hn
      exact (hn hr).elim
  change (Finset.range N).sum (fun r => if p r then H r else 0) *
      (Finset.range N).sum (fun r => if p r then J r else 0) =
      (Finset.range N).sum (fun r => if p r then H r * J r else 0)
  by_cases hex : ∃ r ∈ Finset.range N, p r
  · obtain ⟨r, hr, hp⟩ := hex
    rw [hsingle H r hr hp, hsingle J r hr hp,
      hsingle (fun s => H s * J s) r hr hp]
  · have hzero (C : ℕ → ℝ) :
        (Finset.range N).sum (fun r => if p r then C r else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have hnot : ¬p r := by
        intro hp
        exact hex ⟨r, hr, hp⟩
      exact if_neg hnot
    rw [hzero H, hzero J, hzero (fun r => H r * J r)]
    ring
