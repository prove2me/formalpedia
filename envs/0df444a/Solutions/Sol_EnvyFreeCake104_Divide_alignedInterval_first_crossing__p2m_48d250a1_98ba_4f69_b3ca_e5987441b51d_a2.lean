-- Prove2me | solution 1 for EnvyFreeCake104.Divide.alignedInterval_first_crossing__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T01:56:28.35465+00:00
-- url     : https://prove2.me/submissions/7b41a394-c1c0-4c87-aa97-98b640420224

import Definitions.Def_EnvyFreeCake104_Divide_Query
import Theorems.Thm_EnvyFreeCake104_Divide_cell_partition_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
import Theorems.Thm_EnvyFreeCake104_Divide_aligned_cell_prefix_accounting__p2m_ee4ea07c_74b1_4666_9e33_804cbad52afb_a1

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

-- Pure residual search; no sign assumption on the individual entries is needed.
lemma findCell_residual_decomposition__p2m_ee4ea07c_74b1_4666_9e33_804cbad52afb_a1
    {ι : Type} (s : Rec ι) (i : ι) (L : List ℝ) (r : ℝ)
    (hr : 0 < r) (htotal : r ≤ (L.map (s.val i)).sum) :
    ∃ (pre post : List ℝ) (c t : ℝ),
      L = pre ++ c :: post ∧ findCell s i L r = some (c, t) ∧
      0 < t ∧ t ≤ s.val i c ∧ (pre.map (s.val i)).sum + t = r := by
  induction L generalizing r with
  | nil =>
      simp only [List.map_nil, List.sum_nil] at htotal
      linarith
  | cons c rest ih =>
      by_cases h : r ≤ s.val i c
      · refine ⟨[], rest, c, r, rfl, ?_, hr, h, ?_⟩
        · simp only [findCell, if_pos h]
        · simp
      · have hr' : 0 < r - s.val i c := by linarith
        have ht' : r - s.val i c ≤ (rest.map (s.val i)).sum := by
          simp only [List.map_cons, List.sum_cons] at htotal
          linarith
        obtain ⟨pre, post, d, t, hL, hf, ht, htv, heq⟩ := ih (r - s.val i c) hr' ht'
        refine ⟨c :: pre, post, d, t, ?_, ?_, ht, htv, ?_⟩
        · simp only [List.cons_append, hL]
        · simpa only [findCell, if_neg h] using hf
        · simp only [List.map_cons, List.sum_cons]
          linarith

theorem solution
    {ι : Type} (V : ι → Valuation) (N : Finset ι)
    (s : Rec ι) (hs : s.Valid V N) (i : ι) (hi : i ∈ N)
    (hcut : ∀ (a b r : ℝ), 0 ≤ a → a ≤ b → b ≤ 1 →
      0 ≤ r → r ≤ (V i).value (Set.Ico a b) →
      a ≤ cutAnswer V i a r ∧ cutAnswer V i a r ≤ b ∧
      (V i).value (Set.Ico a (cutAnswer V i a r)) = r ∧
      ∀ z : ℝ, z ∈ Set.Icc a b →
        r ≤ (V i).value (Set.Ico a z) → cutAnswer V i a r ≤ z)
    (I : Interval) (hI : 0 ≤ I.a ∧ I.a ≤ I.b ∧ I.b ≤ 1)
    (ha : I.a ∈ s.pts) (hb : I.b ∈ s.pts)
    (r : ℝ) (hr : 0 ≤ r) (hrI : r ≤ s.intervalVal i I) :
    ∃ x : ℝ,
      (if r ≤ 0 then some I.a else
        match findCell s i
            ((s.pts.filter (fun c => I.a ≤ c ∧ c < I.b)).sort (· ≤ ·)) r with
        | none => none
        | some (c, t) => some (cutAnswer V i c t)) = some x ∧
      I.a ≤ x ∧ x ≤ I.b ∧ (V i).value (Set.Ico I.a x) = r ∧
      ∀ z : ℝ, z ∈ Set.Icc I.a I.b →
        r ≤ (V i).value (Set.Ico I.a z) → x ≤ z := by
  classical
  by_cases hz : r ≤ 0
  · have hr0 : r = 0 := le_antisymm hz hr
    refine ⟨I.a, ?_, le_rfl, hI.2.1, ?_, ?_⟩
    · simp only [if_pos hz]
    · simp [hr0, Valuation.value]
    · intro z hzi _
      exact hzi.1
  · have hrpos : 0 < r := lt_of_not_ge hz
    let F := s.pts.filter (fun c ↦ I.a ≤ c ∧ c < I.b)
    let L := F.sort (· ≤ ·)
    have hsum : (L.map (s.val i)).sum = s.intervalVal i I := by
      simpa only [L, Finset.sort_toFinset, Rec.intervalVal, F] using
        (List.sum_toFinset (s.val i) (F.sort_nodup (· ≤ ·))).symm
    have htotal : r ≤ (L.map (s.val i)).sum := by
      rw [hsum]
      exact hrI
    obtain ⟨pre, post, c, t, hL, hf, ht, htv, heq⟩ :=
      findCell_residual_decomposition__p2m_ee4ea07c_74b1_4666_9e33_804cbad52afb_a1
        s i L r hrpos htotal
    obtain ⟨hc, hac, hcd, hdb, hprefix⟩ :=
      EnvyFreeCake104.Divide.aligned_cell_prefix_accounting__p2m_ee4ea07c_74b1_4666_9e33_804cbad52afb_a1
        V N s hs i hi I hI ha hb pre post c hL
    have hc0 : 0 ≤ c := le_trans hI.1 hac
    have hd1 : s.nextPt c ≤ 1 := le_trans hdb hI.2.2
    have hc1 : c < 1 := lt_of_lt_of_le hcd hd1
    have hv : s.val i c = (V i).value (Set.Ico c (s.nextPt c)) :=
      hs.2.2.2 i hi c hc hc1
    have htcell : t ≤ (V i).value (Set.Ico c (s.nextPt c)) := by
      rw [← hv]
      exact htv
    obtain ⟨hcx, hxd, hxval, hleast⟩ :=
      hcut c (s.nextPt c) t hc0 (le_of_lt hcd) hd1 (le_of_lt ht) htcell
    have hax : I.a ≤ cutAnswer V i c t := le_trans hac hcx
    have hxb : cutAnswer V i c t ≤ I.b := le_trans hxd hdb
    refine ⟨cutAnswer V i c t, ?_, hax, hxb, ?_, ?_⟩
    · change (if r ≤ 0 then some I.a else
        match findCell s i L r with
        | none => none
        | some (c, t) => some (cutAnswer V i c t)) = _
      rw [if_neg hz, hf]
    · rw [(hprefix _ ⟨hax, hxb⟩).2 hcx, hxval]
      exact heq
    · intro z hzI hrz
      by_cases hzc : z ≤ c
      · have hbound := (hprefix z hzI).1 hzc
        have : False := by linarith
        exact this.elim
      · have hcz : c ≤ z := le_of_lt (lt_of_not_ge hzc)
        by_cases hzd : z ≤ s.nextPt c
        · apply hleast z ⟨hcz, hzd⟩
          have hsplit := (hprefix z hzI).2 hcz
          linarith
        · exact le_trans hxd (le_of_lt (lt_of_not_ge hzd))
