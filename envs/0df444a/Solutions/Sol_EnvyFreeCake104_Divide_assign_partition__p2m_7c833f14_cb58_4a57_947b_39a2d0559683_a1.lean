-- Prove2me | solution 1 for EnvyFreeCake104.Divide.assign_partition__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T07:10:32.507974+00:00
-- url     : https://prove2.me/submissions/cd9a6bcd-f5f8-4d79-8ef1-01027b70cae5

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

open EnvyFreeCake104.Divide

set_option autoImplicit false

private theorem assign_mem__p2m_3d245ed7_e7ef_4932_be64_c4d1b3593bc7_a1
    {ι : Type} [DecidableEq ι] (l : List ι) :
    ∀ (ps : List Piece), ps.length = l.length →
      ∀ i ∈ l, assign l ps i ∈ ps := by
  induction l with
  | nil =>
      intro ps hlen i hi
      simp at hi
  | cons a l ih =>
      intro ps hlen
      cases ps with
      | nil => simp at hlen
      | cons P ps =>
          have ht : ps.length = l.length := Nat.succ.inj hlen
          intro i hi
          by_cases hia : i = a
          · subst i
            simp [assign]
          · have hil : i ∈ l := (List.mem_cons.mp hi).resolve_left hia
            simpa [assign, hia] using
              (List.mem_cons_of_mem P (ih ps ht i hil))

private theorem assign_surjective__p2m_3d245ed7_e7ef_4932_be64_c4d1b3593bc7_a1
    {ι : Type} [DecidableEq ι] (l : List ι) :
    ∀ (ps : List Piece), l.Nodup → ps.length = l.length →
      ∀ P ∈ ps, ∃ i ∈ l, assign l ps i = P := by
  induction l with
  | nil =>
      intro ps hn hlen
      have hp : ps = [] := List.length_eq_zero_iff.mp hlen
      subst ps
      simp
  | cons a l ih =>
      intro ps hn hlen
      cases ps with
      | nil => simp
      | cons P ps =>
          have ht : ps.length = l.length := Nat.succ.inj hlen
          have hn' := List.nodup_cons.mp hn
          intro R hR
          rcases List.mem_cons.mp hR with hR | hR
          · subst R
            exact ⟨a, by simp, by simp [assign]⟩
          · obtain ⟨i, hi, he⟩ := ih ps hn'.2 ht R hR
            have hia : i ≠ a := by
              intro h
              subst i
              exact hn'.1 hi
            refine ⟨i, List.mem_cons_of_mem a hi, ?_⟩
            simpa [assign, hia] using he

private theorem assign_disjoint__p2m_3d245ed7_e7ef_4932_be64_c4d1b3593bc7_a1
    {ι : Type} [DecidableEq ι] (l : List ι) :
    ∀ (ps : List Piece), l.Nodup → ps.length = l.length →
      ps.Pairwise (fun P R ↦ Disjoint P.toSet R.toSet) →
      ∀ i ∈ l, ∀ j ∈ l, i ≠ j →
        Disjoint (assign l ps i).toSet (assign l ps j).toSet := by
  induction l with
  | nil =>
      intro ps hn hlen hd i hi
      simp at hi
  | cons a l ih =>
      intro ps hn hlen hd
      cases ps with
      | nil => simp at hlen
      | cons P ps =>
          have ht : ps.length = l.length := Nat.succ.inj hlen
          have hn' := List.nodup_cons.mp hn
          have hd' := List.pairwise_cons.mp hd
          intro i hi j hj hij
          by_cases hia : i = a
          · subst i
            have hja : j ≠ a := Ne.symm hij
            have hjl : j ∈ l := (List.mem_cons.mp hj).resolve_left hja
            have hm := assign_mem__p2m_3d245ed7_e7ef_4932_be64_c4d1b3593bc7_a1
              l ps ht j hjl
            simpa [assign, hja] using hd'.1 (assign l ps j) hm
          · have hil : i ∈ l := (List.mem_cons.mp hi).resolve_left hia
            by_cases hja : j = a
            · subst j
              have hm := assign_mem__p2m_3d245ed7_e7ef_4932_be64_c4d1b3593bc7_a1
                l ps ht i hil
              simpa [assign, hia] using (hd'.1 (assign l ps i) hm).symm
            · have hjl : j ∈ l := (List.mem_cons.mp hj).resolve_left hja
              simpa [assign, hia, hja] using ih ps hn'.2 ht hd'.2 i hil j hjl hij

theorem solution
    {ι : Type} [DecidableEq ι] (N : Finset ι) (ps : List Piece)
    (hlen : ps.length = N.card) (s : Rec ι) (v : Valuation) (w : ℝ) (Q : Set ℝ)
    (hwf : ∀ P ∈ ps, P.WF) (halign : ∀ P ∈ ps, s.Aligned P)
    (hdis : ps.Pairwise (fun P R ↦ Disjoint P.toSet R.toSet))
    (hcover : (⋃ P ∈ ps, P.toSet) = Q) (hval : ∀ P ∈ ps, v.value P.toSet = w) :
    (∀ i ∈ N, (assign N.toList ps i).WF) ∧
    (∀ i ∈ N, s.Aligned (assign N.toList ps i)) ∧
    (∀ i ∈ N, ∀ j ∈ N, i ≠ j →
      Disjoint (assign N.toList ps i).toSet (assign N.toList ps j).toSet) ∧
    (⋃ i ∈ N, (assign N.toList ps i).toSet) = Q ∧
    (∀ i ∈ N, v.value (assign N.toList ps i).toSet = w) := by
  have hl : ps.length = N.toList.length := by simpa using hlen
  have hm : ∀ i ∈ N, assign N.toList ps i ∈ ps := by
    intro i hi
    exact assign_mem__p2m_3d245ed7_e7ef_4932_be64_c4d1b3593bc7_a1
      N.toList ps hl i (Finset.mem_toList.mpr hi)
  have hs : ∀ P ∈ ps, ∃ i ∈ N, assign N.toList ps i = P := by
    intro P hP
    obtain ⟨i, hi, he⟩ :=
      assign_surjective__p2m_3d245ed7_e7ef_4932_be64_c4d1b3593bc7_a1
        N.toList ps N.nodup_toList hl P hP
    exact ⟨i, Finset.mem_toList.mp hi, he⟩
  refine ⟨fun i hi ↦ hwf _ (hm i hi), fun i hi ↦ halign _ (hm i hi), ?_, ?_,
    fun i hi ↦ hval _ (hm i hi)⟩
  · intro i hi j hj hij
    exact assign_disjoint__p2m_3d245ed7_e7ef_4932_be64_c4d1b3593bc7_a1
      N.toList ps N.nodup_toList hl hdis i (Finset.mem_toList.mpr hi)
        j (Finset.mem_toList.mpr hj) hij
  · calc
      (⋃ i ∈ N, (assign N.toList ps i).toSet) = ⋃ P ∈ ps, P.toSet := by
        ext x
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨i, hi, hx⟩
          exact ⟨assign N.toList ps i, hm i hi, hx⟩
        · rintro ⟨P, hP, hx⟩
          obtain ⟨i, hi, he⟩ := hs P hP
          exact ⟨i, hi, by simpa only [he] using hx⟩
      _ = Q := hcover
