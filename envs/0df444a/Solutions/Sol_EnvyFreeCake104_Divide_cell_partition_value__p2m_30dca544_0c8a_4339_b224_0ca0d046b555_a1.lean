-- Prove2me | solution 1 for EnvyFreeCake104.Divide.cell_partition_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T19:17:01.917814+00:00
-- url     : https://prove2.me/submissions/b077259d-742f-4b2d-8d56-d9118318d31c

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution
    {ι : Type} (v : Valuation) (s : Rec ι) (I : Interval)
    (hpts : ∀ c ∈ s.pts, 0 ≤ c ∧ c ≤ 1)
    (ha : I.a ∈ s.pts) (hb : I.b ∈ s.pts) (hab : I.a ≤ I.b) :
    (∑ c ∈ s.pts.filter (fun c ↦ I.a ≤ c ∧ c < I.b),
      v.value (Set.Ico c (s.nextPt c))) = v.value I.toSet := by
  classical
  -- Any recorded point strictly to the right bounds the successor from above.
  have hnext (c d : ℝ) (hd : d ∈ s.pts) (hcd : c < d) :
      c < s.nextPt c ∧ s.nextPt c ∈ s.pts ∧ s.nextPt c ≤ d := by
    have hn : (s.pts.filter (fun e ↦ c < e)).Nonempty :=
      ⟨d, Finset.mem_filter.mpr ⟨hd, hcd⟩⟩
    have hm := Finset.min'_mem (s.pts.filter (fun e ↦ c < e)) hn
    have hmin := Finset.mem_filter.mp hm
    simpa only [Rec.nextPt, dif_pos hn] using
      (show c < (s.pts.filter (fun e ↦ c < e)).min' hn ∧
        (s.pts.filter (fun e ↦ c < e)).min' hn ∈ s.pts ∧
        (s.pts.filter (fun e ↦ c < e)).min' hn ≤ d from
        ⟨hmin.2, hmin.1,
          Finset.min'_le _ d (Finset.mem_filter.mpr ⟨hd, hcd⟩)⟩)
  let t := s.pts.filter (fun c ↦ I.a ≤ c ∧ c < I.b)
  have ht (c : ℝ) (hc : c ∈ t) : c ∈ s.pts ∧ I.a ≤ c ∧ c < I.b := by
    exact Finset.mem_filter.mp hc
  have hcell (c : ℝ) (hc : c ∈ t) :
      Set.Ico c (s.nextPt c) ⊆ Set.Ico I.a I.b := by
    intro x hx
    exact ⟨(ht c hc).2.1.trans hx.1,
      hx.2.trans_le (hnext c I.b hb (ht c hc).2.2).2.2⟩
  have hcover : (⋃ c ∈ t, Set.Ico c (s.nextPt c)) = Set.Ico I.a I.b := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨c, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨hc, hx⟩
      exact hcell c hc hx
    · intro hx
      -- The greatest recorded point at most x is the unique cell start containing x.
      let q := s.pts.filter (fun c ↦ c ≤ x)
      have hq : q.Nonempty := ⟨I.a, Finset.mem_filter.mpr ⟨ha, hx.1⟩⟩
      let c := q.max' hq
      have hcq : c ∈ q := Finset.max'_mem q hq
      have hcpts : c ∈ s.pts := (Finset.mem_filter.mp hcq).1
      have hcx : c ≤ x := (Finset.mem_filter.mp hcq).2
      have hac : I.a ≤ c :=
        Finset.le_max' q I.a (Finset.mem_filter.mpr ⟨ha, hx.1⟩)
      have hcb : c < I.b := hcx.trans_lt hx.2
      have hn := hnext c I.b hb hcb
      have hxn : x < s.nextPt c := by
        by_contra h
        have hnq : s.nextPt c ∈ q := Finset.mem_filter.mpr ⟨hn.2.1, le_of_not_gt h⟩
        have hnc : s.nextPt c ≤ c := Finset.le_max' q (s.nextPt c) hnq
        exact (not_lt_of_ge hnc) hn.1
      exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨hcpts, hac, hcb⟩, ⟨hcx, hxn⟩⟩⟩
  have hdisj : Set.Pairwise (↑t)
      (fun c d ↦ Disjoint (Set.Ico c (s.nextPt c)) (Set.Ico d (s.nextPt d))) := by
    intro c hc d hd hne
    apply Set.disjoint_left.mpr
    intro x hxc hxd
    rcases lt_or_gt_of_ne hne with hcd | hdc
    · have hnd := (hnext c d (ht d hd).1 hcd).2.2
      exact (not_lt_of_ge (hnd.trans hxd.1)) hxc.2
    · have hnc := (hnext d c (ht c hc).1 hdc).2.2
      exact (not_lt_of_ge (hnc.trans hxc.1)) hxd.2
  have hIco : Set.Ico I.a I.b ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨(hpts I.a ha).1.trans hx.1, hx.2.le.trans (hpts I.b hb).2⟩
  have hIcc : Set.Icc I.a I.b ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨(hpts I.a ha).1.trans hx.1, hx.2.trans (hpts I.b hb).2⟩
  have hcake (c : ℝ) (hc : c ∈ t) :
      Set.Ico c (s.nextPt c) ⊆ Set.Icc (0 : ℝ) 1 :=
    (hcell c hc).trans hIco
  change (∑ c ∈ t, v.value (Set.Ico c (s.nextPt c))) = v.value I.toSet
  calc
    (∑ c ∈ t, v.value (Set.Ico c (s.nextPt c))) =
        ∑ c ∈ t, ∫ x in Set.Ico c (s.nextPt c), v.density x := by
      apply Finset.sum_congr rfl
      intro c hc
      unfold Valuation.value
      rw [Set.inter_eq_left.mpr (hcake c hc)]
    _ = ∫ x in Set.Ico I.a I.b, v.density x := by
      rw [← hcover]
      exact (MeasureTheory.integral_biUnion_finset t (fun _ _ ↦ measurableSet_Ico)
        hdisj (fun c hc ↦ v.integrable.mono_set (hcake c hc))).symm
    _ = v.value I.toSet := by
      unfold Valuation.value Interval.toSet
      split_ifs with h
      · rw [Set.inter_eq_left.mpr hIcc]
        exact MeasureTheory.integral_Icc_eq_integral_Ico.symm
      · rw [Set.inter_eq_left.mpr hIco]
