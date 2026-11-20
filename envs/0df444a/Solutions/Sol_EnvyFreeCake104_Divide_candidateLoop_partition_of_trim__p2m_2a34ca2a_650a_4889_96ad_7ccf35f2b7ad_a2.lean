-- Prove2me | solution 1 for EnvyFreeCake104.Divide.candidateLoop_partition_of_trim__p2m_2a34ca2a_650a_4889_96ad_7ccf35f2b7ad_a2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T16:14:30.925183+00:00
-- url     : https://prove2.me/submissions/4325a44d-612b-4381-8fe5-aff7174fd1d8

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

open EnvyFreeCake104.Divide

namespace CLPAux

theorem run_bind {ι α β : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (p : Prog ι α) (f : α → Prog ι β) (tr : List (Event ι)) :
    Prog.run V o (Prog.bind p f) tr =
      match Prog.run V o p tr with
      | none => none
      | some (x, tr') => Prog.run V o (f x) tr' := by
  induction p generalizing tr with
  | ret x => rfl
  | fail => rfl
  | eval i a b k ih =>
      simp only [Prog.bind, Prog.run]
      exact ih (evalAnswer V i a b) (tr ++ [Event.eval i a b (evalAnswer V i a b)])
  | cut i x w k ih =>
      simp only [Prog.bind, Prog.run]
      exact ih (cutAnswer V i x w) (tr ++ [Event.cut i x w (cutAnswer V i x w)])
  | choose m k ih =>
      simp only [Prog.bind, Prog.run]
      exact ih (o tr m) (tr ++ [Event.choice m (o tr m)])

theorem toSet_append (A B : Piece) : Piece.toSet (A ++ B) = A.toSet ∪ B.toSet := by
  ext x; simp [Piece.toSet, or_and_right, exists_or]

theorem toSet_nil : Piece.toSet [] = ∅ := by
  ext x; simp [Piece.toSet]

theorem aligned_mono {ι : Type} (s t : Rec ι) (h : s.pts ⊆ t.pts) (P : Piece)
    (hP : s.Aligned P) : t.Aligned P := fun I hI => ⟨h (hP I hI).1, h (hP I hI).2⟩

end CLPAux

open CLPAux in
theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (htrim : ∀ (A : ι → Piece) (hA : ∀ i ∈ N, (A i).WF)
      (earlier : List ι) (hearlier : ∀ i ∈ earlier, i ∈ N)
      (Q : Piece) (hQ : Q.WF) (t : Rec ι) (ht : t.Valid V N)
      (hAt : ∀ i ∈ N, t.Aligned (A i)) (hQt : t.Aligned Q)
      (o : ChoiceOracle ι) (tr₀ : List (Event ι))
      (B rem : Piece) (t' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((trimAgainst N A earlier Q []).run t) tr₀ =
        some (((B, rem), t'), tr) →
      t'.Valid V N ∧ t.pts ⊆ t'.pts ∧ B.WF ∧ t'.Aligned B ∧
        Disjoint B.toSet rem.toSet ∧ B.toSet ∪ rem.toSet = Q.toSet)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j →
      Disjoint (P i).toSet (P j).toSet)
    (pairs : List (ι × ι))
    (hag : (pairs.map Prod.fst).Nodup)
    (hagents : ∀ q ∈ pairs, q.1 ∈ N)
    (hpieces : (pairs.map Prod.snd).Perm N.toList)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (o : ChoiceOracle ι) (tr₀ : List (Event ι))
    (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : Prog.run V o
      ((candidateLoop N P pairs [] (fun _ ↦ []) []).run s) tr₀ =
        some (((Y, R), s'), tr)) :
    R.toSet ∪ (⋃ i ∈ N, (Y i).toSet) = (⋃ i ∈ N, (P i).toSet) ∧
      Disjoint R.toSet (⋃ i ∈ N, (Y i).toSet) := by
  have hpcN : ∀ q ∈ pairs, q.2 ∈ N := fun q hq => by
    have : q.2 ∈ pairs.map Prod.snd := List.mem_map_of_mem hq
    rw [hpieces.mem_iff, Finset.mem_toList] at this; exact this
  have hpcnd : (pairs.map Prod.snd).Nodup := hpieces.nodup_iff.mpr (Finset.nodup_toList N)
  -- generalized invariant
  have key : ∀ (pairs : List (ι × ι)), (pairs.map Prod.fst).Nodup → (∀ q ∈ pairs, q.1 ∈ N) →
      (pairs.map Prod.snd).Nodup → (∀ q ∈ pairs, q.2 ∈ N) →
      ∀ (earlier : List ι) (Y0 : ι → Piece) (R0 : Piece) (t : Rec ι) (o : ChoiceOracle ι)
        (tr₀ : List (Event ι)) (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι)),
      (∀ i ∈ earlier, i ∈ N) → t.Valid V N → (∀ i ∈ N, t.Aligned (P i)) →
      (∀ i ∈ N, (Y0 i).WF ∧ t.Aligned (Y0 i)) →
      (∀ q ∈ pairs, Y0 q.1 = []) →
      Disjoint R0.toSet (⋃ i ∈ N, (Y0 i).toSet) →
      (∀ q ∈ pairs, Disjoint (P q.2).toSet (R0.toSet ∪ ⋃ i ∈ N, (Y0 i).toSet)) →
      Prog.run V o ((candidateLoop N P pairs earlier Y0 R0).run t) tr₀ = some (((Y, R), s'), tr) →
      R.toSet ∪ (⋃ i ∈ N, (Y i).toSet) =
          (R0.toSet ∪ ⋃ i ∈ N, (Y0 i).toSet) ∪ ⋃ q ∈ pairs, (P q.2).toSet ∧
        Disjoint R.toSet (⋃ i ∈ N, (Y i).toSet) := by
    intro pairs
    induction pairs with
    | nil =>
      intro _ _ _ _ earlier Y0 R0 t o tr₀ Y R s' tr _ _ _ _ _ hdR _ hr
      simp only [candidateLoop] at hr
      change Prog.run V o (Prog.ret ((Y0, R0), t)) tr₀ = _ at hr
      simp only [Prog.run, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hr
      simp [hdR]
    | cons q rest ih =>
      obtain ⟨i, j⟩ := q
      intro hag hagents hpnd hpcN earlier Y0 R0 t o tr₀ Y R s' tr hear ht hPt hY0 hemp hdR hdP hr
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hag hpnd
      have hiN : i ∈ N := hagents _ (List.mem_cons_self ..)
      have hjN : j ∈ N := hpcN _ (List.mem_cons_self ..)
      simp only [candidateLoop] at hr
      change Prog.run V o (Prog.bind ((trimAgainst N Y0 earlier (P j) []).run t)
        (fun p => (candidateLoop N P rest (earlier ++ [i]) (Function.update Y0 i p.1.1)
          (R0 ++ p.1.2)).run p.2)) tr₀ = _ at hr
      rw [run_bind] at hr
      rcases htr : Prog.run V o ((trimAgainst N Y0 earlier (P j) []).run t) tr₀ with
        _ | ⟨⟨⟨B, rem⟩, t1⟩, tr1⟩
      · rw [htr] at hr; exact absurd hr (by simp)
      rw [htr] at hr
      simp only at hr
      obtain ⟨ht1, hsub, hBwf, hBal, hBrem, hBremU⟩ :=
        htrim Y0 (fun k hk => (hY0 k hk).1) earlier hear (P j) (hP j hjN) t ht
          (fun k hk => (hY0 k hk).2) (hPt j hjN) o tr₀ B rem t1 tr1 htr
      have hY0i : (Y0 i).toSet = ∅ := by rw [hemp (i, j) (List.mem_cons_self ..)]; exact toSet_nil
      have hU : (⋃ k ∈ N, (Function.update Y0 i B k).toSet) = B.toSet ∪ ⋃ k ∈ N, (Y0 k).toSet := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_union, exists_prop]
        constructor
        · rintro ⟨k, hk, hx⟩
          by_cases hki : k = i
          · subst hki; simp at hx; exact Or.inl hx
          · rw [Function.update_of_ne hki] at hx; exact Or.inr ⟨k, hk, hx⟩
        · rintro (hx | ⟨k, hk, hx⟩)
          · exact ⟨i, hiN, by simpa using hx⟩
          · have hki : k ≠ i := by rintro rfl; rw [hY0i] at hx; exact hx
            exact ⟨k, hk, by rwa [Function.update_of_ne hki]⟩
      have hBsub : B.toSet ⊆ (P j).toSet := hBremU ▸ Set.subset_union_left
      have hremsub : rem.toSet ⊆ (P j).toSet := hBremU ▸ Set.subset_union_right
      have hdPj := hdP (i, j) (List.mem_cons_self ..)
      obtain ⟨hres1, hres2⟩ := ih hag.2 (fun q hq => hagents q (List.mem_cons_of_mem _ hq)) hpnd.2
        (fun q hq => hpcN q (List.mem_cons_of_mem _ hq)) (earlier ++ [i])
        (Function.update Y0 i B) (R0 ++ rem) t1 o tr1 Y R s' tr
        (by intro k hk; rw [List.mem_append] at hk; rcases hk with hk | hk
            · exact hear k hk
            · simp at hk; exact hk ▸ hiN)
        ht1 (fun k hk => aligned_mono t t1 hsub _ (hPt k hk))
        (by intro k hk
            by_cases hki : k = i
            · subst hki; simp [hBwf, hBal]
            · rw [Function.update_of_ne hki]
              exact ⟨(hY0 k hk).1, aligned_mono t t1 hsub _ (hY0 k hk).2⟩)
        (by intro q hq
            have hne : q.1 ≠ i := by
              rintro h; exact hag.1 ⟨q, hq, h⟩
            rw [Function.update_of_ne hne]; exact hemp q (List.mem_cons_of_mem _ hq))
        (by rw [hU, toSet_append]
            refine Disjoint.union_left (Disjoint.union_right ?_ ?_) (Disjoint.union_right ?_ ?_)
            · exact (Disjoint.mono_right hBsub (Disjoint.mono_right Set.subset_union_left hdPj).symm)
            · exact hdR
            · exact hBrem.symm
            · exact Disjoint.mono_left hremsub
                (Disjoint.mono_right Set.subset_union_right hdPj))
        (by intro q hq
            have hqN := hpcN q (List.mem_cons_of_mem _ hq)
            have hqj : q.2 ≠ j := by rintro h; exact hpnd.1 ⟨q, hq, h⟩
            have hdj := hPdisj q.2 hqN j hjN hqj
            have hdq := hdP q (List.mem_cons_of_mem _ hq)
            rw [hU, toSet_append]
            refine Disjoint.union_right (Disjoint.union_right ?_ ?_) (Disjoint.union_right ?_ ?_)
            · exact Disjoint.mono_right Set.subset_union_left hdq
            · exact Disjoint.mono_right hremsub hdj
            · exact Disjoint.mono_right hBsub hdj
            · exact Disjoint.mono_right Set.subset_union_right hdq)
        hr
      refine ⟨?_, hres2⟩
      rw [hres1, hU, toSet_append]
      ext x
      simp only [Set.mem_union, Set.mem_iUnion, List.mem_cons, exists_prop]
      constructor
      · rintro ((((h | h) | (h | h)) | ⟨q, hq, h⟩))
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨(i, j), Or.inl rfl, hremsub h⟩
        · exact Or.inr ⟨(i, j), Or.inl rfl, hBsub h⟩
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨q, Or.inr hq, h⟩
      · rintro ((h | h) | ⟨q, hq | hq, h⟩)
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr h))
        · subst hq
          rw [← hBremU] at h
          rcases h with h | h
          · exact Or.inl (Or.inr (Or.inl h))
          · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inr ⟨q, hq, h⟩
  obtain ⟨h1, h2⟩ := key pairs hag hagents hpcnd hpcN [] (fun _ => []) [] s o tr₀ Y R s' tr
    (by simp) hs hPs (by intro i _; simp [Piece.WF, Rec.Aligned]) (fun _ _ => rfl)
    (by simp [toSet_nil]) (by intro q _; simp [toSet_nil]) hrun
  refine ⟨?_, h2⟩
  rw [h1]
  simp only [toSet_nil, Set.empty_union, Set.iUnion_empty]
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨q, hq, hx⟩; exact ⟨q.2, hpcN q hq, hx⟩
  · rintro ⟨j, hj, hx⟩
    have : j ∈ pairs.map Prod.snd := by rw [hpieces.mem_iff, Finset.mem_toList]; exact hj
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp this
    exact ⟨q, hq, hx⟩
