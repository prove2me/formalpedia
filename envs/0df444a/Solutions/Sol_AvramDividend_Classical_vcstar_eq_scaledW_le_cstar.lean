-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_eq_scaledW_le_cstar
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:35:43.847693+00:00
-- url     : https://prove2.me/submissions/99b35304-fd7e-4a67-833a-81c1b345f8b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution :
    ¬ (∀ (W : ℝ → ℝ) (z : ℝ) (hz : z ≤ (cstar W).toReal),
      vcstar W z = divE (W z) (scaleDeriv W (cstar W).toReal)) := by
  intro H
  set W : ℝ → ℝ := fun x => x with hW
  have hd : ∀ y, deriv W y = 1 := fun y => by simp [hW]
  have hset : cstarSet W = Ioi 0 := by
    ext a; simp [cstarSet, hd]
  have hc : cstar W = 0 := by
    unfold cstar
    rw [if_pos (by rw [hset]; exact ⟨1, show (0:ℝ) < 1 from one_pos⟩), hset]
    by_contra hne
    have hpos : 0 < ⨅ a ∈ Ioi (0:ℝ), ENNReal.ofReal a := pos_iff_ne_zero.2 hne
    obtain ⟨ε, hε0, hεc⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε < ⨅ a ∈ Ioi (0:ℝ), ENNReal.ofReal a := by
      obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hpos
      exact ⟨r, ENNReal.ofReal_pos.1 hr1, hr2⟩
    exact absurd (iInf₂_le ε (show ε ∈ Ioi (0:ℝ) from hε0)) (not_le.2 hεc)
  have hct : (cstar W).toReal = 0 := by rw [hc]; rfl
  have hsd : scaleDeriv W 0 = ((1 : ℝ) : EReal) := by
    unfold scaleDeriv derivZeroPlus
    simp only [if_true, hd]
    exact Filter.liminf_const _
  have key := H W (-1) (by rw [hct]; norm_num)
  rw [hct, hsd] at key
  have h1 : vcstar W (-1) = 0 := by
    unfold vcstar barrierValue; rw [hct]; simp
  have h2 : divE (W (-1)) ((1 : ℝ) : EReal) = -1 := by
    unfold divE; rw [if_neg (EReal.coe_ne_top 1)]; simp [hW]
  rw [h1, h2] at key; norm_num at key
