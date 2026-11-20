-- Prove2me | solution 1 for EnvyFreeCake104.Divide.trimAgainst_partition__p2m_2a34ca2a_650a_4889_96ad_7ccf35f2b7ad_a2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T16:17:01.342427+00:00
-- url     : https://prove2.me/submissions/7b2c485c-78bb-4035-aebb-648b12f6df1b

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
import Theorems.Thm_EnvyFreeCake104_Divide_cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
import Theorems.Thm_EnvyFreeCake104_Divide_recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1

open EnvyFreeCake104.Divide

namespace TAPAux

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

end TAPAux

open TAPAux in
theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) :
    ∀ (A : ι → Piece) (hA : ∀ i ∈ N, (A i).WF)
      (earlier : List ι) (hearlier : ∀ i ∈ earlier, i ∈ N)
      (Q : Piece) (hQ : Q.WF) (t : Rec ι) (ht : t.Valid V N)
      (hAt : ∀ i ∈ N, t.Aligned (A i)) (hQt : t.Aligned Q)
      (o : ChoiceOracle ι) (tr₀ : List (Event ι))
      (B rem : Piece) (t' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((trimAgainst N A earlier Q []).run t) tr₀ =
        some (((B, rem), t'), tr) →
      t'.Valid V N ∧ t.pts ⊆ t'.pts ∧ B.WF ∧ t'.Aligned B ∧
        Disjoint B.toSet rem.toSet ∧ B.toSet ∪ rem.toSet = Q.toSet := by
  intro A hA earlier
  -- generalized statement with an arbitrary accumulator `R0`
  have key : ∀ (earlier : List ι), (∀ i ∈ earlier, i ∈ N) →
      ∀ (Q R0 : Piece) (t : Rec ι) (o : ChoiceOracle ι) (tr₀ : List (Event ι))
        (B rem : Piece) (t' : Rec ι) (tr : List (Event ι)),
      Q.WF → t.Valid V N → (∀ i ∈ N, t.Aligned (A i)) → t.Aligned Q →
      Disjoint Q.toSet R0.toSet →
      Prog.run V o ((trimAgainst N A earlier Q R0).run t) tr₀ = some (((B, rem), t'), tr) →
      t'.Valid V N ∧ t.pts ⊆ t'.pts ∧ B.WF ∧ t'.Aligned B ∧
        Disjoint B.toSet rem.toSet ∧ B.toSet ∪ rem.toSet = Q.toSet ∪ R0.toSet := by
    intro earlier
    induction earlier with
    | nil =>
      intro _ Q R0 t o tr₀ B rem t' tr hQ ht _ hQt hd hr
      simp only [trimAgainst] at hr
      change Prog.run V o (Prog.ret ((Q, R0), t)) tr₀ = _ at hr
      simp only [Prog.run, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hr
      exact ⟨ht, subset_rfl, hQ, hQt, hd, rfl⟩
    | cons a rest ih =>
      intro hear Q R0 t o tr₀ B rem t' tr hQ ht hAt hQt hd hr
      have haN : a ∈ N := hear a (List.mem_cons_self ..)
      have hrest : ∀ i ∈ rest, i ∈ N := fun i hi => hear i (List.mem_cons_of_mem _ hi)
      simp only [trimAgainst, StateT.run_bind, StateT.run_get] at hr
      change Prog.run V o (StateT.run (if 0 < t.pieceVal a Q - t.pieceVal a (A a) then
          (do let p ← prefixCut N a Q (t.pieceVal a Q - t.pieceVal a (A a))
              trimAgainst N A rest (suffixList Q p) (R0 ++ prefixList Q p))
        else trimAgainst N A rest Q R0) t) tr₀ = _ at hr
      split_ifs at hr with hpos
      · rw [StateT.run_bind] at hr
        change Prog.run V o (Prog.bind ((prefixCut N a Q _).run t)
          (fun p => (trimAgainst N A rest (suffixList Q p.1) (R0 ++ prefixList Q p.1)).run p.2))
          tr₀ = _ at hr
        rw [run_bind] at hr
        have hvQ := recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
          V N t ht a haN Q hQ hQt
        have hvA := recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
          V N t ht a haN (A a) (hA a haN) (hAt a haN)
        obtain ⟨p, t1, tr1, hpc, ht1, hsub, hvp, hpal, hsal, -, -⟩ :=
          prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1 V N a haN Q hQ t ht
            hQt (t.pieceVal a Q - t.pieceVal a (A a)) hpos.le
            (by rw [hvQ, hvA]; linarith [value_nonneg (V a) (A a)]) o tr₀
        rw [hpc] at hr
        simp only at hr
        -- partition of Q at p
        have hpart : (prefixList Q p).WF ∧ (suffixList Q p).WF ∧
            Disjoint (prefixList Q p).toSet (suffixList Q p).toSet ∧
            (prefixList Q p).toSet ∪ (suffixList Q p).toSet = Q.toSet := by
          rcases hvp with rfl | hvp
          · simp [prefixList, suffixList, Piece.WF, toSet_nil]
          · exact cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1 Q hQ p hvp
        obtain ⟨hpwf, hswf, hpsd, hpsu⟩ := hpart
        have hssub : (suffixList Q p).toSet ⊆ Q.toSet := hpsu ▸ Set.subset_union_right
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih hrest (suffixList Q p) (R0 ++ prefixList Q p) t1 o tr1
          B rem t' tr hswf ht1 (fun i hi => aligned_mono t t1 hsub _ (hAt i hi)) hsal
          (by rw [toSet_append]
              exact Disjoint.union_right (Disjoint.mono_left hssub hd) hpsd.symm) hr
        refine ⟨h1, hsub.trans h2, h3, h4, h5, ?_⟩
        rw [h6, toSet_append, ← hpsu]
        ext x; simp only [Set.mem_union]; tauto
      · exact ih hrest Q R0 t o tr₀ B rem t' tr hQ ht hAt hQt hd hr
  intro hear Q hQ t ht hAt hQt o tr₀ B rem t' tr hr
  have := key earlier hear Q [] t o tr₀ B rem t' tr hQ ht hAt hQt (by simp [toSet_nil]) hr
  simpa [toSet_nil] using this
