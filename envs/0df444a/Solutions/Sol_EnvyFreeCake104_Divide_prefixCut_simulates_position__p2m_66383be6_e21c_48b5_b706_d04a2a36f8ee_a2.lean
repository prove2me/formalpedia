-- Prove2me | solution 1 for EnvyFreeCake104.Divide.prefixCut_simulates_position__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T01:32:08.380462+00:00
-- url     : https://prove2.me/submissions/5d79e821-01a9-4cd7-a831-5a354dc0062f

import Definitions.Def_EnvyFreeCake104_Divide_Query
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_endpoint_recording__p2m_8c415f54_233a_4754_8600_5f90a07d6713_a1

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

/-- A successful positive cell search selects a positive amount within that cell's value. -/
theorem EnvyFreeCake104.Divide.findCell_positive_selected__p2m_8c415f54_233a_4754_8600_5f90a07d6713_a1
    {ι : Type} (s : Rec ι) (i : ι) (cs : List ℝ) (r c t : ℝ)
    (hr : 0 < r) (h : findCell s i cs r = some (c, t)) :
    c ∈ cs ∧ 0 < t ∧ t ≤ s.val i c := by
  induction cs generalizing r with
  | nil => cases h
  | cons d ds ih =>
    rw [findCell] at h
    split at h
    · rename_i hd
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨by simp, hr, hd⟩
    · rename_i hd
      obtain ⟨hc, ht, htc⟩ :=
        ih (r - s.val i d) (sub_pos.mpr (lt_of_not_ge hd)) h
      exact ⟨List.mem_cons_of_mem d hc, ht, htc⟩

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hsplit : ∀ (t : Rec ι), t.Valid V N →
      ∀ (c y : ℝ), c ∈ t.pts → c < y → y < t.nextPt c →
      ∀ (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
      ∃ (t' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((splitCell N c y).run t) tr₀ = some (((), t'), tr) ∧
        t'.Valid V N ∧ t'.pts = insert y t.pts)
    (i : ι) (hi : i ∈ N)
    (hcut : ∀ (a b r : ℝ), 0 ≤ a → a ≤ b → b ≤ 1 →
      0 ≤ r → r ≤ (V i).value (Set.Ico a b) →
      a ≤ cutAnswer V i a r ∧ cutAnswer V i a r ≤ b ∧
      (V i).value (Set.Ico a (cutAnswer V i a r)) = r ∧
      ∀ z : ℝ, z ∈ Set.Icc a b →
        r ≤ (V i).value (Set.Ico a z) → cutAnswer V i a r ≤ z)
    (Q : Piece) (hQ : Q.WF) (s : Rec ι)
    (hs : s.Valid V N) (hQs : s.Aligned Q)
    (w : ℝ) (hw : 0 ≤ w) (p : Pos)
    (hp : (match findInterval s i Q 0 w with
        | none => if w ≤ 0 then some (Q.length, (0 : ℝ)) else none
        | some (k, r) =>
          if r ≤ 0 then some (k, (Q.getD k default).a)
          else
            match findCell s i
                ((s.pts.filter (fun c => (Q.getD k default).a ≤ c ∧
                  c < (Q.getD k default).b)).sort (· ≤ ·)) r with
            | none => none
            | some (c, t) => some (k, cutAnswer V i c t)) = some p)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι)) :
    ∃ (s' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((prefixCut N i Q w).run s) tr₀ = some ((p, s'), tr) ∧
      s'.Valid V N ∧ s.pts ⊆ s'.pts ∧
      s'.Aligned (prefixList Q p) ∧ s'.Aligned (suffixList Q p) := by
  classical
  have hsafe : ∀ I ∈ Q, ∀ (r : ℝ), 0 < r → ∀ (c t : ℝ),
      findCell s i
        ((s.pts.filter (fun c => I.a ≤ c ∧ c < I.b)).sort (· ≤ ·)) r =
          some (c, t) →
      c ∈ s.pts ∧
        (cutAnswer V i c t ∈ s.pts ∨
          (c < cutAnswer V i c t ∧ cutAnswer V i c t < s.nextPt c)) := by
    intro I hI r hr c t hf
    obtain ⟨hcmem, ht, htv⟩ :=
      EnvyFreeCake104.Divide.findCell_positive_selected__p2m_8c415f54_233a_4754_8600_5f90a07d6713_a1 s i _ r c t hr hf
    have hc : c ∈ s.pts ∧ I.a ≤ c ∧ c < I.b := by
      simpa only [Finset.mem_sort, Finset.mem_filter] using hcmem
    have hb : I.b ∈ s.pts := (hQs I hI).2
    have hne : (s.pts.filter (fun d : ℝ => c < d)).Nonempty :=
      ⟨I.b, Finset.mem_filter.mpr ⟨hb, hc.2.2⟩⟩
    have hnext : s.nextPt c ∈ s.pts ∧ c < s.nextPt c := by
      have hm := Finset.mem_filter.mp
        (Finset.min'_mem (s.pts.filter (fun d : ℝ => c < d)) hne)
      simpa only [Rec.nextPt, dif_pos hne] using hm
    have hc1 : c < 1 := lt_of_lt_of_le hc.2.2 (hs.2.2.1 I.b hb).2
    have hrec := hs.2.2.2 i hi c hc.1 hc1
    have htval : t ≤ (V i).value (Set.Ico c (s.nextPt c)) := by
      simpa only [hrec] using htv
    have hbds := hcut c (s.nextPt c) t (hs.2.2.1 c hc.1).1
      (le_of_lt hnext.2) (hs.2.2.1 (s.nextPt c) hnext.1).2 (le_of_lt ht) htval
    refine ⟨hc.1, ?_⟩
    by_cases hyc : cutAnswer V i c t = c
    · left
      rw [hyc]
      exact hc.1
    by_cases hyn : cutAnswer V i c t = s.nextPt c
    · left
      rw [hyn]
      exact hnext.1
    · right
      exact ⟨lt_of_le_of_ne hbds.1 (Ne.symm hyc), lt_of_le_of_ne hbds.2.1 hyn⟩
  obtain ⟨s', tr, hrun, hs', hext, hpoint⟩ :=
    EnvyFreeCake104.Divide.prefixCut_endpoint_recording__p2m_8c415f54_233a_4754_8600_5f90a07d6713_a1 V N hsplit i Q s hs
      (fun I hI ↦ (hQs I hI).1) hsafe w p hp o tr₀
  have hQa : s'.Aligned Q := by
    intro I hI
    exact ⟨hext (hQs I hI).1, hext (hQs I hI).2⟩
  have hget (hk : p.1 < Q.length) : Q.getD p.1 default ∈ Q := by
    rw [List.getD_eq_getElem Q default hk]
    exact List.getElem_mem hk
  refine ⟨s', tr, hrun, hs', hext, ?_, ?_⟩
  · intro I hI
    by_cases hk : p.1 < Q.length
    · simp only [prefixList, if_pos hk, List.mem_append, List.mem_singleton] at hI
      rcases hI with hI | rfl
      · exact hQa I (List.take_subset p.1 Q hI)
      · exact ⟨(hQa _ (hget hk)).1, hpoint hk⟩
    · have hIQ : I ∈ Q := by simpa only [prefixList, if_neg hk] using hI
      exact hQa I hIQ
  · intro I hI
    by_cases hk : p.1 < Q.length
    · simp only [suffixList, if_pos hk, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact ⟨hpoint hk, (hQa _ (hget hk)).2⟩
      · exact hQa I (List.drop_subset (p.1 + 1) Q hI)
    · simp [suffixList, hk] at hI
