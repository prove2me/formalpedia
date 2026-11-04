-- Prove2me | solution 1 for CryptoMembership.PerfectInfo.eq15_root_statics
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:05:35.711426+00:00
-- url     : https://prove2.me/submissions/da12b073-5041-4889-9203-b645d3f2ec47

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model
import Theorems.Thm_CryptoMembership_PerfectInfo_lhs15_log_concave_bell

open CryptoMembership.PerfectInfo

namespace RootStaticsAux

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

end RootStaticsAux

open RootStaticsAux in
theorem solution (P : Params) (hP : P.Standing) :
    (∀ A xi A' xi' : ℝ, A + xi < A' + xi' → rhs15 P A' xi' < rhs15 P A xi) ∧
    ∀ sHat : ℝ, (∀ t : ℝ, lhs15 P t ≤ lhs15 P sHat) →
      (∀ R R' s s' : ℝ, 0 < R' → R' < R → lhs15 P s = R → lhs15 P s' = R' →
          s ≤ sHat → s' ≤ sHat → s' < s) ∧
      (∀ R R' s s' : ℝ, 0 < R' → R' < R → lhs15 P s = R → lhs15 P s' = R' →
          sHat ≤ s → sHat ≤ s' → s < s') := by
  refine ⟨fun A xi A' xi' h => ?_, fun sHat hmax => ⟨?_, ?_⟩⟩
  · unfold rhs15
    exact Real.exp_lt_exp.2 (by linarith)
  · intro R R' s s' _ hRR hs hs' hsle hs'le
    by_contra hcon
    push Not at hcon
    rcases hcon.lt_or_eq with h | h
    · have := side_left P hP sHat hmax h hs'le
      linarith
    · rw [h] at hs; linarith
  · intro R R' s s' _ hRR hs hs' hsle hs'le
    by_contra hcon
    push Not at hcon
    rcases hcon.lt_or_eq with h | h
    · have := side_right P hP sHat hmax hs'le h
      linarith
    · rw [h] at hs'; linarith
