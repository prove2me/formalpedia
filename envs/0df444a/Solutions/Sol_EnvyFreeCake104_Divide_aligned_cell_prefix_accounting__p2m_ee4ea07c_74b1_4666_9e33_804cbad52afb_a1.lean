-- Prove2me | solution 1 for EnvyFreeCake104.Divide.aligned_cell_prefix_accounting__p2m_ee4ea07c_74b1_4666_9e33_804cbad52afb_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T02:07:58.166197+00:00
-- url     : https://prove2.me/submissions/41fc6353-f2f5-405a-918f-cf4c1d8ae8b1

import Definitions.Def_EnvyFreeCake104_Divide_Query
import Theorems.Thm_EnvyFreeCake104_Divide_cell_partition_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

theorem solution
    {ι : Type} (V : ι → Valuation) (N : Finset ι)
    (s : Rec ι) (hs : s.Valid V N) (i : ι) (hi : i ∈ N)
    (I : Interval) (hI : 0 ≤ I.a ∧ I.a ≤ I.b ∧ I.b ≤ 1)
    (ha : I.a ∈ s.pts) (hb : I.b ∈ s.pts)
    (pre post : List ℝ) (c : ℝ)
    (hlist : ((s.pts.filter (fun d ↦ I.a ≤ d ∧ d < I.b)).sort (· ≤ ·)) =
      pre ++ c :: post) :
    c ∈ s.pts ∧ I.a ≤ c ∧ c < s.nextPt c ∧ s.nextPt c ≤ I.b ∧
      ∀ z : ℝ, z ∈ Set.Icc I.a I.b →
        (z ≤ c → (V i).value (Set.Ico I.a z) ≤ (pre.map (s.val i)).sum) ∧
        (c ≤ z → (V i).value (Set.Ico I.a z) =
          (pre.map (s.val i)).sum + (V i).value (Set.Ico c z)) := by
  classical
  rcases hs with ⟨hzero, hone, hpts, hval⟩
  let F := s.pts.filter (fun d ↦ I.a ≤ d ∧ d < I.b)
  have hcF : c ∈ F := by
    apply (Finset.mem_sort (s := F) (r := (· ≤ ·))).mp
    change c ∈ (s.pts.filter (fun d ↦ I.a ≤ d ∧ d < I.b)).sort (· ≤ ·)
    rw [hlist]
    simp
  obtain ⟨hc, hac, hcb⟩ := Finset.mem_filter.mp hcF
  have hc1 : c < 1 := lt_of_lt_of_le hcb hI.2.2

  -- The right endpoint supplies a genuine successor of c in the record table.
  have hne : (s.pts.filter (fun d ↦ c < d)).Nonempty :=
    ⟨I.b, Finset.mem_filter.mpr ⟨hb, hcb⟩⟩
  have hnext : s.nextPt c = (s.pts.filter (fun d ↦ c < d)).min' hne := by
    unfold Rec.nextPt
    rw [dif_pos hne]
  have hcnext : c < s.nextPt c := by
    rw [hnext]
    exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  have hnextb : s.nextPt c ≤ I.b := by
    rw [hnext]
    exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hb, hcb⟩)

  -- Sorting is strict because the source is a finset, so pre is exactly [I.a,c).
  have hstrict : (pre ++ c :: post).Pairwise (· < ·) := by
    rw [← hlist]
    exact List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort _)
  have hnodup : (pre ++ c :: post).Nodup := by
    rw [← hlist]
    exact Finset.sort_nodup _ _
  have hpre : pre.toFinset = s.pts.filter (fun d ↦ I.a ≤ d ∧ d < c) := by
    ext x
    constructor
    · intro hx
      have hxpre : x ∈ pre := List.mem_toFinset.mp hx
      have hxall : x ∈ F.sort (· ≤ ·) := by
        change x ∈ (s.pts.filter (fun d ↦ I.a ≤ d ∧ d < I.b)).sort (· ≤ ·)
        rw [hlist]
        exact List.mem_append.mpr (Or.inl hxpre)
      have hxF : x ∈ F := (Finset.mem_sort _).mp hxall
      obtain ⟨hxs, hax, _⟩ := Finset.mem_filter.mp hxF
      have hxc : x < c :=
        (List.pairwise_append.mp hstrict).2.2 x hxpre c (by simp)
      exact Finset.mem_filter.mpr ⟨hxs, hax, hxc⟩
    · intro hx
      obtain ⟨hxs, hax, hxc⟩ := Finset.mem_filter.mp hx
      have hxF : x ∈ F := Finset.mem_filter.mpr ⟨hxs, hax, lt_trans hxc hcb⟩
      have hxall : x ∈ pre ++ c :: post := by
        rw [← hlist]
        exact (Finset.mem_sort _).mpr hxF
      rcases List.mem_append.mp hxall with hxpre | hxpost
      · exact List.mem_toFinset.mpr hxpre
      · rcases List.mem_cons.mp hxpost with hxc' | hxpost
        · exact False.elim ((ne_of_lt hxc) hxc')
        · have hcx : c < x :=
            (List.pairwise_cons.mp (List.pairwise_append.mp hstrict).2.1).1 x hxpost
          exact False.elim ((not_lt_of_ge (le_of_lt hcx)) hxc)

  have hsum : (pre.map (s.val i)).sum = (V i).value (Set.Ico I.a c) := by
    calc
      (pre.map (s.val i)).sum = ∑ x ∈ pre.toFinset, s.val i x :=
        (List.sum_toFinset (s.val i) (List.nodup_append'.mp hnodup).1).symm
      _ = ∑ x ∈ s.pts.filter (fun d ↦ I.a ≤ d ∧ d < c), s.val i x := by rw [hpre]
      _ = ∑ x ∈ s.pts.filter (fun d ↦ I.a ≤ d ∧ d < c),
          (V i).value (Set.Ico x (s.nextPt x)) := by
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨hxs, _, hxc⟩ := Finset.mem_filter.mp hx
        exact hval i hi x hxs (lt_trans hxc hc1)
      _ = (V i).value (Set.Ico I.a c) := by
        simpa [Interval.toSet, ne_of_lt hc1] using
          (cell_partition_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
            (V i) s ⟨I.a, c⟩ hpts ha hc hac)

  refine ⟨hc, hac, hcnext, hnextb, ?_⟩
  intro z hz
  constructor
  · intro hzc
    rw [hsum]
    unfold Valuation.value
    apply MeasureTheory.setIntegral_mono_set
      ((V i).integrable.mono_set Set.inter_subset_right)
    · exact (MeasureTheory.ae_restrict_mem
        (measurableSet_Ico.inter measurableSet_Icc)).mono
          (fun x hx ↦ (V i).nonneg x hx.2)
    · exact Filter.Eventually.of_forall (fun x hx ↦
        ⟨⟨hx.1.1, lt_of_lt_of_le hx.1.2 hzc⟩, hx.2⟩)
  · intro hcz
    rw [hsum]
    unfold Valuation.value
    have hunion :
        (Set.Ico I.a c ∩ Set.Icc (0 : ℝ) 1) ∪
          (Set.Ico c z ∩ Set.Icc (0 : ℝ) 1) =
        Set.Ico I.a z ∩ Set.Icc (0 : ℝ) 1 := by
      rw [← Set.union_inter_distrib_right, Set.Ico_union_Ico_eq_Ico hac hcz]
    rw [← hunion]
    apply MeasureTheory.setIntegral_union
    · apply Set.disjoint_left.mpr
      intro x hx hy
      exact (not_lt_of_ge hy.1.1) hx.1.2
    · exact measurableSet_Ico.inter measurableSet_Icc
    · exact (V i).integrable.mono_set Set.inter_subset_right
    · exact (V i).integrable.mono_set Set.inter_subset_right
