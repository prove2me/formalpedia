-- Prove2me | solution 1 for AvramDividend.Classical.chat05_rightCont_prefixSup_encoded_onSample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:13:01.028822+00:00
-- url     : https://prove2.me/submissions/b18758c4-64fd-4467-8591-f91a6b948f39

import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
import Theorems.Thm_AvramDividend_Classical_countable_bddRealSup_eq_ennrealOfRealSup_toReal

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    (f : ℝ≥0 → ℝ)
    (hr : ∀ u, ContinuousWithinAt f (Ici u) u)
    (hf0 : f 0 = 0)
    (samples : ℕ → ℝ≥0)
    (hdense : Dense (Set.range samples))
    (hzero : (0 : ℝ≥0) ∈ Set.range samples)
    (t : ℝ≥0) (ht : t ∈ Set.range samples)
    (hb : BddAbove (Set.range
      (fun s : Set.Icc (0 : ℝ≥0) t => f s.1))) :
    (⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1) =
      (⨆ j : ℕ, ENNReal.ofReal
        (if samples j ≤ t then max 0 (f (samples j)) else 0)).toReal := by
  set A := ⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1 with hA
  have hle : ∀ s : ℝ≥0, s ≤ t → f s ≤ A := fun s hs =>
    le_ciSup hb (⟨s, (zero_le (a := s)), hs⟩ : Set.Icc (0 : ℝ≥0) t)
  have hA0 : 0 ≤ A := hf0 ▸ hle 0 ((zero_le (a := t)))
  set g : ℕ → ℝ := fun j => if samples j ≤ t then max 0 (f (samples j)) else 0 with hg
  have hgA : ∀ j, g j ≤ A := by
    intro j; simp only [hg]; split_ifs with h
    · exact max_le hA0 (hle _ h)
    · exact hA0
  have hgb : BddAbove (Set.range g) := ⟨A, by rintro _ ⟨j, rfl⟩; exact hgA j⟩
  have hg0 : ∀ j, 0 ≤ g j := by
    intro j; simp only [hg]; split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  have hfg : ∀ j, samples j ≤ t → f (samples j) ≤ ⨆ i, g i := by
    intro j hj
    refine le_trans ?_ (le_ciSup hgb j)
    simp only [hg, if_pos hj]; exact le_max_right _ _
  rw [AvramDividend.Classical.countable_bddRealSup_eq_ennrealOfRealSup_toReal g hgb
    (le_trans (hg0 0) (le_ciSup hgb 0))]
  refine le_antisymm ?_ (ciSup_le hgA)
  rw [hA, AvramDividend.Classical.dense_timeSup_with_endpoint f hr _ hdense hzero t hb]
  refine max_le ?_ ?_
  · have : Nonempty {s : ℝ≥0 // s ∈ Set.range samples ∧ s ≤ t} := ⟨⟨0, hzero, (zero_le (a := t))⟩⟩
    refine ciSup_le fun s => ?_
    obtain ⟨⟨j, hj⟩, hst⟩ := s.2
    rw [← hj]; exact hfg j (hj ▸ hst)
  · obtain ⟨j, hj⟩ := ht
    rw [← hj]; exact hfg j (hj ▸ le_rfl)
