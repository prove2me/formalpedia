-- Prove2me | solution 1 for CryptoMembership.PerfectInfo.eq15_root_count
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:06:40.801811+00:00
-- url     : https://prove2.me/submissions/e0b4d04f-9fc7-45bf-8919-d4286605dd52

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model
import Theorems.Thm_CryptoMembership_PerfectInfo_lhs15_log_concave_bell

open CryptoMembership.PerfectInfo Filter Topology

namespace RootCountAux

theorem side_left (P : Params) (hP : P.Standing) (sHat : ℝ)
    (hmax : ∀ t, lhs15 P t ≤ lhs15 P sHat)
    {x y : ℝ} (hxy : x < y) (hy : y ≤ sHat) : lhs15 P x < lhs15 P y := by
  obtain ⟨hpos, hconc, -, -⟩ := lhs15_log_concave_bell P hP
  have hfx : Real.log (lhs15 P x) ≤ Real.log (lhs15 P sHat) :=
    Real.log_le_log (hpos x) (hmax x)
  rw [← Real.log_lt_log_iff (hpos x) (hpos y)]
  have hxs : x < sHat := lt_of_lt_of_le hxy hy
  rcases hy.lt_or_eq with hy | hy
  · have hd : 0 < sHat - x := by linarith
    have ha : 0 < (sHat - y) / (sHat - x) := div_pos (by linarith) hd
    have hb : 0 < (y - x) / (sHat - x) := div_pos (by linarith) hd
    have hab : (sHat - y) / (sHat - x) + (y - x) / (sHat - x) = 1 := by
      field_simp; ring
    have hcomb : (sHat - y) / (sHat - x) * x + (y - x) / (sHat - x) * sHat = y := by
      field_simp; ring
    have := hconc.2 (Set.mem_univ x) (Set.mem_univ sHat) hxs.ne ha hb hab
    simp only [smul_eq_mul] at this
    rw [hcomb] at this
    have k1 := mul_le_mul_of_nonneg_left hfx hb.le
    have k2 : (sHat - y) / (sHat - x) * Real.log (lhs15 P x) +
        (y - x) / (sHat - x) * Real.log (lhs15 P x) = Real.log (lhs15 P x) := by
      rw [← add_mul, hab, one_mul]
    linarith
  · rw [hy]
    have := hconc.2 (Set.mem_univ x) (Set.mem_univ sHat) hxs.ne
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    have hm := Real.log_le_log (hpos _) (hmax ((1/2:ℝ) * x + 1/2 * sHat))
    linarith

theorem side_right (P : Params) (hP : P.Standing) (sHat : ℝ)
    (hmax : ∀ t, lhs15 P t ≤ lhs15 P sHat)
    {x y : ℝ} (hx : sHat ≤ x) (hxy : x < y) : lhs15 P y < lhs15 P x := by
  obtain ⟨hpos, hconc, -, -⟩ := lhs15_log_concave_bell P hP
  have hfy : Real.log (lhs15 P y) ≤ Real.log (lhs15 P sHat) :=
    Real.log_le_log (hpos y) (hmax y)
  rw [← Real.log_lt_log_iff (hpos y) (hpos x)]
  have hys : sHat < y := lt_of_le_of_lt hx hxy
  rcases hx.lt_or_eq with hx | hx
  · have hd : 0 < y - sHat := by linarith
    have ha : 0 < (y - x) / (y - sHat) := div_pos (by linarith) hd
    have hb : 0 < (x - sHat) / (y - sHat) := div_pos (by linarith) hd
    have hab : (y - x) / (y - sHat) + (x - sHat) / (y - sHat) = 1 := by
      field_simp; ring
    have hcomb : (y - x) / (y - sHat) * sHat + (x - sHat) / (y - sHat) * y = x := by
      field_simp; ring
    have := hconc.2 (Set.mem_univ sHat) (Set.mem_univ y) hys.ne ha hb hab
    simp only [smul_eq_mul] at this
    rw [hcomb] at this
    have k1 := mul_le_mul_of_nonneg_left hfy ha.le
    have k2 : (y - x) / (y - sHat) * Real.log (lhs15 P y) +
        (x - sHat) / (y - sHat) * Real.log (lhs15 P y) = Real.log (lhs15 P y) := by
      rw [← add_mul, hab, one_mul]
    linarith
  · rw [← hx]
    have := hconc.2 (Set.mem_univ sHat) (Set.mem_univ y) hys.ne
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    have hm := Real.log_le_log (hpos _) (hmax ((1/2:ℝ) * sHat + 1/2 * y))
    linarith

theorem lhs15_continuous (P : Params) (hP : P.Standing) : Continuous (lhs15 P) := by
  obtain ⟨hpos, hconc, -, -⟩ := lhs15_log_concave_bell P hP
  have hc : ContinuousOn (fun s => Real.log (lhs15 P s)) Set.univ :=
    hconc.concaveOn.continuousOn isOpen_univ
  have : lhs15 P = fun s => Real.exp (Real.log (lhs15 P s)) := by
    funext s; rw [Real.exp_log (hpos s)]
  rw [this]
  exact Real.continuous_exp.comp (continuousOn_univ.1 hc)

theorem exists_max (P : Params) (hP : P.Standing) :
    ∃ sHat : ℝ, ∀ s : ℝ, lhs15 P s ≤ lhs15 P sHat := by
  obtain ⟨hpos, -, hbot, htop⟩ := lhs15_log_concave_bell P hP
  have hc := lhs15_continuous P hP
  set v := lhs15 P 0
  have hv : 0 < v := hpos 0
  obtain ⟨T1, hT1⟩ := Filter.eventually_atBot.1 (hbot.eventually (gt_mem_nhds hv))
  obtain ⟨T2, hT2⟩ := Filter.eventually_atTop.1 (htop.eventually (gt_mem_nhds hv))
  obtain ⟨m, hm, hmax⟩ := (isCompact_Icc (a := min T1 0) (b := max T2 0)).exists_isMaxOn
    ⟨0, by simp⟩ hc.continuousOn
  refine ⟨m, fun s => ?_⟩
  have h0 : lhs15 P 0 ≤ lhs15 P m := hmax (by simp)
  by_cases hs : s ∈ Set.Icc (min T1 0) (max T2 0)
  · exact hmax hs
  · simp only [Set.mem_Icc, not_and_or, not_le] at hs
    rcases hs with hs | hs
    · have := hT1 s (le_of_lt (lt_of_lt_of_le hs (min_le_left _ _)))
      linarith
    · have := hT2 s (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hs))
      linarith

end RootCountAux

open RootCountAux in
theorem solution (P : Params) (hP : P.Standing) :
    ∃ sHat : ℝ, (∀ s : ℝ, lhs15 P s ≤ lhs15 P sHat) ∧
      ∀ R : ℝ, 0 < R →
        ({s : ℝ | lhs15 P s = R}.encard = 2 ↔ R < lhs15 P sHat) ∧
        ({s : ℝ | lhs15 P s = R}.encard = 1 ↔ R = lhs15 P sHat) ∧
        ({s : ℝ | lhs15 P s = R}.encard = 0 ↔ lhs15 P sHat < R) := by
  obtain ⟨sHat, hmax⟩ := exists_max P hP
  obtain ⟨hpos, -, hbot, htop⟩ := lhs15_log_concave_bell P hP
  have hc := lhs15_continuous P hP
  refine ⟨sHat, hmax, fun R hR => ?_⟩
  set M := lhs15 P sHat
  -- case R < M
  have c2 : R < M → {s : ℝ | lhs15 P s = R}.encard = 2 := by
    intro hRM
    obtain ⟨x0, hx0⟩ := ((hbot.eventually (gt_mem_nhds hR)).and
      (eventually_lt_atBot sHat)).exists
    obtain ⟨y0, hy0⟩ := ((htop.eventually (gt_mem_nhds hR)).and
      (eventually_gt_atTop sHat)).exists
    obtain ⟨s1, hs1, hs1R⟩ := intermediate_value_Icc hx0.2.le hc.continuousOn
      (⟨hx0.1.le, hRM.le⟩ : R ∈ Set.Icc (lhs15 P x0) (lhs15 P sHat))
    obtain ⟨s2, hs2, hs2R⟩ := intermediate_value_Icc' hy0.2.le hc.continuousOn
      (⟨hy0.1.le, hRM.le⟩ : R ∈ Set.Icc (lhs15 P y0) (lhs15 P sHat))
    have hs1' : s1 < sHat := lt_of_le_of_ne hs1.2 (by rintro rfl; linarith)
    have hs2' : sHat < s2 := lt_of_le_of_ne hs2.1 (by rintro rfl; linarith)
    rw [Set.encard_eq_two]
    refine ⟨s1, s2, by linarith, ?_⟩
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ht
      rcases lt_trichotomy t sHat with h | h | h
      · left
        rcases lt_trichotomy t s1 with h' | h' | h'
        · have := side_left P hP sHat hmax h' hs1'.le; linarith
        · exact h'
        · have := side_left P hP sHat hmax h' h.le; linarith
      · rw [h] at ht; linarith
      · right
        rcases lt_trichotomy t s2 with h' | h' | h'
        · have := side_right P hP sHat hmax h.le h'; linarith
        · exact h'
        · have := side_right P hP sHat hmax hs2'.le h'; linarith
    · rintro (rfl | rfl) <;> assumption
  -- case R = M
  have c1 : R = M → {s : ℝ | lhs15 P s = R}.encard = 1 := by
    intro hRM
    rw [Set.encard_eq_one]
    refine ⟨sHat, ?_⟩
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro ht
      rcases lt_trichotomy t sHat with h | h | h
      · have := side_left P hP sHat hmax h le_rfl; linarith
      · exact h
      · have := side_right P hP sHat hmax le_rfl h; linarith
    · rintro rfl; exact hRM.symm
  -- case M < R
  have c0 : M < R → {s : ℝ | lhs15 P s = R}.encard = 0 := by
    intro hRM
    rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
    intro t ht
    have := hmax t
    simp only [Set.mem_setOf_eq] at ht
    linarith
  refine ⟨⟨fun h => ?_, c2⟩, ⟨fun h => ?_, c1⟩, ⟨fun h => ?_, c0⟩⟩
  · rcases lt_trichotomy R M with h' | h' | h'
    · exact h'
    · rw [c1 h'] at h; norm_num at h
    · rw [c0 h'] at h; norm_num at h
  · rcases lt_trichotomy R M with h' | h' | h'
    · rw [c2 h'] at h; norm_num at h
    · exact h'
    · rw [c0 h'] at h; norm_num at h
  · rcases lt_trichotomy R M with h' | h' | h'
    · rw [c2 h'] at h; norm_num at h
    · rw [c1 h'] at h; norm_num at h
    · exact h'
