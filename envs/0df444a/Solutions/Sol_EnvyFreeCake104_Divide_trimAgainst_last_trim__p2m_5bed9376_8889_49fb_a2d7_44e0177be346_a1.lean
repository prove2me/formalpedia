-- Prove2me | solution 1 for EnvyFreeCake104.Divide.trimAgainst_last_trim__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T16:21:44.846406+00:00
-- url     : https://prove2.me/submissions/f4b46cf1-e595-4f66-a13b-341dd2b3a618

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
import Theorems.Thm_EnvyFreeCake104_Divide_cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
import Theorems.Thm_EnvyFreeCake104_Divide_recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2

open EnvyFreeCake104.Divide

namespace TLTAux

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

theorem interval_measurable (I : Interval) : MeasurableSet I.toSet := by
  unfold Interval.toSet; split_ifs
  · exact measurableSet_Icc
  · exact measurableSet_Ico

theorem piece_measurable (P : Piece) : MeasurableSet P.toSet := by
  have : P.toSet = ⋃ I ∈ P, I.toSet := by ext x; simp [Piece.toSet]
  rw [this]
  exact MeasurableSet.biUnion P.finite_toSet.countable (fun I _ => interval_measurable I)

theorem value_nonneg (v : Valuation) (P : Piece) : 0 ≤ v.value P.toSet := by
  unfold Valuation.value
  apply MeasureTheory.setIntegral_nonneg ((piece_measurable P).inter measurableSet_Icc)
  intro x hx; exact v.nonneg x hx.2


theorem value_union (v : Valuation) (A B : Piece) (hd : Disjoint A.toSet B.toSet) :
    v.value (A.toSet ∪ B.toSet) = v.value A.toSet + v.value B.toSet := by
  unfold Valuation.value
  rw [Set.union_inter_distrib_right]
  apply MeasureTheory.setIntegral_union
  · exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left hd
  · exact (piece_measurable B).inter measurableSet_Icc
  · exact v.integrable.mono_set Set.inter_subset_right
  · exact v.integrable.mono_set Set.inter_subset_right

end TLTAux

open TLTAux in
theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (Y : ι → Piece) (hY : ∀ i ∈ N, (Y i).WF)
    (earlier : List ι) (hearlier : ∀ i ∈ earlier, i ∈ N)
    (Q removed : Piece) (hQ : Q.WF) (s : Rec ι) (hs : s.Valid V N)
    (hYs : ∀ i ∈ N, s.Aligned (Y i)) (hQs : s.Aligned Q)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι))
    (B rem : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : Prog.run V o ((trimAgainst N Y earlier Q removed).run s) tr₀ =
      some (((B, rem), s'), tr))
    (hchanged : B.toSet ≠ Q.toSet) :
    ∃ j ∈ earlier, (V j).value B.toSet = (V j).value (Y j).toSet := by
  have key : ∀ (earlier : List ι), (∀ i ∈ earlier, i ∈ N) →
      ∀ (Q R0 : Piece) (t : Rec ι) (o : ChoiceOracle ι) (tr₀ : List (Event ι))
        (B rem : Piece) (t' : Rec ι) (tr : List (Event ι)),
      Q.WF → t.Valid V N → (∀ i ∈ N, t.Aligned (Y i)) → t.Aligned Q →
      Prog.run V o ((trimAgainst N Y earlier Q R0).run t) tr₀ = some (((B, rem), t'), tr) →
      B = Q ∨ ∃ j ∈ earlier, (V j).value B.toSet = (V j).value (Y j).toSet := by
    intro earlier
    induction earlier with
    | nil =>
      intro _ Q R0 t o tr₀ B rem t' tr _ _ _ _ hr
      simp only [trimAgainst] at hr
      change Prog.run V o (Prog.ret ((Q, R0), t)) tr₀ = _ at hr
      simp only [Prog.run, Option.some.injEq, Prod.mk.injEq] at hr
      exact Or.inl hr.1.1.1.symm
    | cons a rest ih =>
      intro hear Q R0 t o tr₀ B rem t' tr hQ ht hYt hQt hr
      have haN : a ∈ N := hear a (List.mem_cons_self ..)
      have hrest : ∀ i ∈ rest, i ∈ N := fun i hi => hear i (List.mem_cons_of_mem _ hi)
      simp only [trimAgainst, StateT.run_bind, StateT.run_get] at hr
      change Prog.run V o (StateT.run (if 0 < t.pieceVal a Q - t.pieceVal a (Y a) then
          (do let p ← prefixCut N a Q (t.pieceVal a Q - t.pieceVal a (Y a))
              trimAgainst N Y rest (suffixList Q p) (R0 ++ prefixList Q p))
        else trimAgainst N Y rest Q R0) t) tr₀ = _ at hr
      split_ifs at hr with hpos
      · rw [StateT.run_bind] at hr
        change Prog.run V o (Prog.bind ((prefixCut N a Q _).run t)
          (fun p => (trimAgainst N Y rest (suffixList Q p.1) (R0 ++ prefixList Q p.1)).run p.2))
          tr₀ = _ at hr
        rw [run_bind] at hr
        have hvQ := recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
          V N t ht a haN Q hQ hQt
        have hvA := recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
          V N t ht a haN (Y a) (hY a haN) (hYt a haN)
        obtain ⟨p, t1, tr1, hpc, ht1, hsub, hvp, -, hsal, hpval, -⟩ :=
          prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1 V N a haN Q hQ t ht
            hQt (t.pieceVal a Q - t.pieceVal a (Y a)) hpos.le
            (by rw [hvQ, hvA]; linarith [value_nonneg (V a) (Y a)]) o tr₀
        rw [hpc] at hr
        simp only at hr
        have hpart : (prefixList Q p).WF ∧ (suffixList Q p).WF ∧
            Disjoint (prefixList Q p).toSet (suffixList Q p).toSet ∧
            (prefixList Q p).toSet ∪ (suffixList Q p).toSet = Q.toSet := by
          rcases hvp with rfl | hvp
          · simp [prefixList, suffixList, Piece.WF, toSet_nil]
          · exact cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1 Q hQ p hvp
        obtain ⟨-, hswf, hpsd, hpsu⟩ := hpart
        rcases ih hrest (suffixList Q p) (R0 ++ prefixList Q p) t1 o tr1 B rem t' tr hswf ht1
          (fun i hi => aligned_mono t t1 hsub _ (hYt i hi)) hsal hr with hB | ⟨j, hj, hjv⟩
        · right
          refine ⟨a, List.mem_cons_self .., ?_⟩
          have hadd := value_union (V a) (prefixList Q p) (suffixList Q p) hpsd
          rw [hpsu, hpval, hvQ, hvA] at hadd
          rw [hB]; linarith
        · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hjv⟩
      · rcases ih hrest Q R0 t o tr₀ B rem t' tr hQ ht hYt hQt hr with hB | ⟨j, hj, hjv⟩
        · exact Or.inl hB
        · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hjv⟩
  rcases key earlier hearlier Q removed s o tr₀ B rem s' tr hQ hs hYs hQs hrun with hB | h
  · exact absurd (congrArg Piece.toSet hB) hchanged
  · exact h
