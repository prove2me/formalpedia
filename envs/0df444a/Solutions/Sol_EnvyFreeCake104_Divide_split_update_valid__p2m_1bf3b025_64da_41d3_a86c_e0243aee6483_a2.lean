-- Prove2me | solution 1 for EnvyFreeCake104.Divide.split_update_valid__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T02:09:56.846195+00:00
-- url     : https://prove2.me/submissions/b02aa08c-14ec-4ddb-81c7-8b1a12f88bca

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (s : Rec ι) (hs : s.Valid V N) (c y : ℝ)
    (hc : c ∈ s.pts) (hcy : c < y) (hyn : y < s.nextPt c) :
    ({
             pts := insert y s.pts
             val := fun i x ↦
               if i ∈ N then
                 if x = c then evalAnswer V i c y
                 else if x = y then s.val i c - evalAnswer V i c y
                 else s.val i x
               else s.val i x
             prefixCuts := s.prefixCuts } : Rec ι).Valid V N := by
  classical
  have next_spec (r : Rec ι) (x z : ℝ) (hz : z ∈ r.pts) (hxz : x < z) :
      r.nextPt x ∈ r.pts ∧ x < r.nextPt x ∧
        ∀ w ∈ r.pts, x < w → r.nextPt x ≤ w := by
    have hn : (r.pts.filter (fun w ↦ x < w)).Nonempty :=
      ⟨z, Finset.mem_filter.mpr ⟨hz, hxz⟩⟩
    have hm := Finset.min'_mem (r.pts.filter (fun w ↦ x < w)) hn
    simp only [Rec.nextPt, dif_pos hn]
    refine ⟨(Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2, ?_⟩
    intro w hw hxw
    exact Finset.min'_le _ w (Finset.mem_filter.mpr ⟨hw, hxw⟩)
  have next_eq (r : Rec ι) (x z : ℝ) (hz : z ∈ r.pts) (hxz : x < z)
      (hmin : ∀ w ∈ r.pts, x < w → z ≤ w) : r.nextPt x = z := by
    obtain ⟨hm, hlt, hle⟩ := next_spec r x z hz hxz
    exact le_antisymm (hle z hz hxz) (hmin _ hm hlt)
  have hn : (s.pts.filter (fun w ↦ c < w)).Nonempty := by
    by_contra hn
    have : s.nextPt c = c := by simp [Rec.nextPt, hn]
    rw [this] at hyn
    exact (lt_asymm hcy hyn)
  have hd : s.nextPt c ∈ s.pts := by
    simpa only [Rec.nextPt, dif_pos hn] using
      (Finset.mem_filter.mp (Finset.min'_mem _ hn)).1
  have hcd : c < s.nextPt c := lt_trans hcy hyn
  have hleast := (next_spec s c (s.nextPt c) hd hcd).2.2
  have hc0 : 0 ≤ c := (hs.2.2.1 c hc).1
  have hd1 : s.nextPt c ≤ 1 := (hs.2.2.1 _ hd).2
  have hy0 : 0 ≤ y := le_trans hc0 hcy.le
  have hy1 : y < 1 := lt_of_lt_of_le hyn hd1
  have hc1 : c < 1 := lt_trans hcy hy1
  let t : Rec ι :=
    { pts := insert y s.pts
      val := fun i x ↦ if i ∈ N then
        if x = c then evalAnswer V i c y
        else if x = y then s.val i c - evalAnswer V i c y
        else s.val i x
        else s.val i x
      prefixCuts := s.prefixCuts }
  change t.Valid V N
  have htc : t.nextPt c = y := by
    apply next_eq t c y (by simp [t]) hcy
    intro w hw hcw
    have hw' : w = y ∨ w ∈ s.pts := by simpa [t] using hw
    rcases hw' with rfl | hw'
    · exact le_rfl
    · exact le_trans hyn.le (hleast w hw' hcw)
  have hty : t.nextPt y = s.nextPt c := by
    apply next_eq t y (s.nextPt c) (by simp [t, hd]) hyn
    intro w hw hyw
    have hw' : w = y ∨ w ∈ s.pts := by simpa [t] using hw
    rcases hw' with rfl | hw'
    · exact (lt_irrefl _ hyw).elim
    · exact hleast w hw' (lt_trans hcy hyw)
  have htold : ∀ x ∈ s.pts, x < 1 → x ≠ c → t.nextPt x = s.nextPt x := by
    intro x hx hx1 hxc
    obtain ⟨hm, hlt, hle⟩ := next_spec s x 1 hs.2.1 hx1
    apply next_eq t x (s.nextPt x) (by simp [t, hm]) hlt
    intro w hw hxw
    have hw' : w = y ∨ w ∈ s.pts := by simpa [t] using hw
    rcases hw' with rfl | hw'
    · by_cases hxc' : x < c
      · exact le_trans (hle c hc hxc') hcy.le
      · have hcx : c < x := lt_of_le_of_ne (le_of_not_gt hxc') (Ne.symm hxc)
        have hdx := hleast x hx hcx
        exact (not_lt_of_ge (le_trans hyn.le hdx) hxw).elim
    · exact hle w hw' hxw
  have value_add (v : Valuation) :
      v.value (Set.Ico c (s.nextPt c)) =
        v.value (Set.Ico c y) + v.value (Set.Ico y (s.nextPt c)) := by
    have hu :
        (Set.Ico c y ∩ Set.Icc (0 : ℝ) 1) ∪
            (Set.Ico y (s.nextPt c) ∩ Set.Icc (0 : ℝ) 1) =
          Set.Ico c (s.nextPt c) ∩ Set.Icc (0 : ℝ) 1 := by
      rw [← Set.union_inter_distrib_right, Set.Ico_union_Ico_eq_Ico hcy.le hyn.le]
    have hdis : Disjoint (Set.Ico c y ∩ Set.Icc (0 : ℝ) 1)
        (Set.Ico y (s.nextPt c) ∩ Set.Icc (0 : ℝ) 1) := by
      apply Set.disjoint_left.mpr
      intro z hz hz'
      exact (not_lt_of_ge hz'.1.1) hz.1.2
    unfold Valuation.value
    rw [← hu]
    exact MeasureTheory.setIntegral_union hdis (measurableSet_Ico.inter measurableSet_Icc)
      (v.integrable.mono_set Set.inter_subset_right)
      (v.integrable.mono_set Set.inter_subset_right)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (0 : ℝ) ∈ insert y s.pts
    exact Finset.mem_insert_of_mem hs.1
  · change (1 : ℝ) ∈ insert y s.pts
    exact Finset.mem_insert_of_mem hs.2.1
  · intro x hx
    have hx' : x = y ∨ x ∈ s.pts := by simpa [t] using hx
    rcases hx' with rfl | hx'
    · exact ⟨hy0, hy1.le⟩
    · exact hs.2.2.1 x hx'
  · intro i hi x hx hx1
    by_cases hxc : x = c
    · subst x
      change (if i ∈ N then
        if c = c then evalAnswer V i c y
        else if c = y then s.val i c - evalAnswer V i c y else s.val i c
        else s.val i c) = (V i).value (Set.Ico c (t.nextPt c))
      rw [if_pos hi, if_pos rfl, htc]
      rfl
    · by_cases hxy : x = y
      · subst x
        have hv := hs.2.2.2 i hi c hc hc1
        have ha := value_add (V i)
        change (if i ∈ N then
          if y = c then evalAnswer V i c y
          else if y = y then s.val i c - evalAnswer V i c y else s.val i y
          else s.val i y) = (V i).value (Set.Ico y (t.nextPt y))
        rw [if_pos hi, if_neg hxc, if_pos rfl, hty, hv]
        unfold evalAnswer
        linarith
      · have hxold : x ∈ s.pts := by
          have hx' : x = y ∨ x ∈ s.pts := by simpa [t] using hx
          exact hx'.resolve_left hxy
        have ht := htold x hxold hx1 hxc
        change (if i ∈ N then
          if x = c then evalAnswer V i c y
          else if x = y then s.val i c - evalAnswer V i c y else s.val i x
          else s.val i x) = (V i).value (Set.Ico x (t.nextPt x))
        rw [if_pos hi, if_neg hxc, if_neg hxy, ht]
        exact hs.2.2.2 i hi x hxold hx1
