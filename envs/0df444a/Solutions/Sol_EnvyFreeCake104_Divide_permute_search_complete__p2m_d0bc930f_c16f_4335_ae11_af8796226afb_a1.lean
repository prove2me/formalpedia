-- Prove2me | solution 1 for EnvyFreeCake104.Divide.permute_search_complete__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T16:25:27.092238+00:00
-- url     : https://prove2.me/submissions/70ed9171-8c5f-44f0-8bee-f78047d134d6

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
import Theorems.Thm_EnvyFreeCake104_Divide_cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
import Theorems.Thm_EnvyFreeCake104_Divide_recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2

import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_query_bound__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1
import Theorems.Thm_EnvyFreeCake104_Divide_splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2

open EnvyFreeCake104.Divide

namespace PSCAux

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


section
variable {ι : Type}



/-- A general invariant on a protocol, parametrized by a predicate on (start, end) records and
(start, end) transcripts, closed under bind when the predicate is transitive. -/
def Inv {α : Type} (V : ι → Valuation) (Rel : Rec ι → List (Event ι) → Rec ι → List (Event ι) → Prop)
    (m : Proto ι α) : Prop :=
  ∀ (s : Rec ι) (o : ChoiceOracle ι) (tr₀ : List (Event ι)) (x : α) (s' : Rec ι)
    (tr : List (Event ι)), Prog.run V o (m.run s) tr₀ = some ((x, s'), tr) → Rel s tr₀ s' tr

section
variable (V : ι → Valuation) (Rel : Rec ι → List (Event ι) → Rec ι → List (Event ι) → Prop)
  (hrefl : ∀ s tr, Rel s tr s tr)
  (htrans : ∀ s₁ t₁ s₂ t₂ s₃ t₃, Rel s₁ t₁ s₂ t₂ → Rel s₂ t₂ s₃ t₃ → Rel s₁ t₁ s₃ t₃)
include hrefl

theorem inv_pure {α : Type} (x : α) : Inv V Rel (pure x : Proto ι α) := by
  intro s o tr₀ y s' tr h
  change Prog.run V o (Prog.ret (x, s)) tr₀ = _ at h
  simp only [Prog.run, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, rfl⟩, rfl⟩ := h; exact hrefl _ _

theorem inv_get : Inv V Rel (get : Proto ι (Rec ι)) := by
  intro s o tr₀ y s' tr h
  change Prog.run V o (Prog.ret (s, s)) tr₀ = _ at h
  simp only [Prog.run, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, rfl⟩, rfl⟩ := h; exact hrefl _ _

theorem inv_fail {α : Type} : Inv V Rel (failP : Proto ι α) := by
  intro s o tr₀ y s' tr h
  change Prog.run V o (Prog.bind (Prog.fail : Prog ι α) (fun a => Prog.ret (a, s))) tr₀ = _ at h
  simp [Prog.bind, Prog.run] at h

include htrans in
theorem inv_bind {α β : Type} {m : Proto ι α} {f : α → Proto ι β} (hm : Inv V Rel m)
    (hf : ∀ x, Inv V Rel (f x)) : Inv V Rel (m >>= f) := by
  intro s o tr₀ y s'' tr h
  rw [StateT.run_bind] at h
  change Prog.run V o (Prog.bind (m.run s) (fun p => (f p.1).run p.2)) tr₀ = _ at h
  rw [run_bind] at h
  rcases h1 : Prog.run V o (m.run s) tr₀ with _ | ⟨⟨x, s'⟩, tr1⟩
  · rw [h1] at h; exact absurd h (by simp)
  rw [h1] at h
  exact htrans _ _ _ _ _ _ (hm s o tr₀ x s' tr1 h1) (hf x s' o tr1 y s'' tr h)

theorem inv_ite {α : Type} (c : Prop) [Decidable c] {a b : Proto ι α} (ha : Inv V Rel a)
    (hb : Inv V Rel b) : Inv V Rel (if c then a else b) := by
  split_ifs; exacts [ha, hb]
end

def PC0 : Rec ι → List (Event ι) → Rec ι → List (Event ι) → Prop :=
  fun s _ s' _ => s'.prefixCuts = s.prefixCuts

theorem pc0_refl : ∀ (s : Rec ι) tr, PC0 s tr s tr := fun _ _ => rfl
theorem pc0_trans : ∀ (s₁ : Rec ι) t₁ s₂ t₂ s₃ t₃, PC0 s₁ t₁ s₂ t₂ →
    PC0 s₂ t₂ s₃ t₃ → PC0 s₁ t₁ s₃ t₃ := fun _ _ _ _ _ _ h1 h2 => h2.trans h1

theorem cut_pc0 (V : ι → Valuation) (i : ι) (x w : ℝ) : Inv V PC0 (cutQ i x w : Proto ι ℝ) := by
  intro s o tr₀ y s' tr h
  change Prog.run V o (Prog.bind (Prog.cut i x w Prog.ret) (fun a => Prog.ret (a, s))) tr₀ = _ at h
  simp only [Prog.bind, Prog.run, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, rfl⟩, rfl⟩ := h; rfl

theorem split_pc0 [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) (c y : ℝ) :
    Inv V PC0 (splitCell N c y) := by
  intro s o tr₀ u s' tr h
  obtain ⟨tr', h'⟩ :=
    splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2 V N s c y o tr₀
  rw [h'] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, rfl⟩, -⟩ := h; rfl

theorem prefixCut_pc [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) (i : ι) (P : Piece)
    (w : ℝ) : Inv V (fun s _ s' _ => s'.prefixCuts = s.prefixCuts + 1) (prefixCut N i P w) := by
  intro s o tr₀ p s' tr h
  simp only [prefixCut, StateT.run_bind, StateT.run_modify, StateT.run_get] at h
  change Prog.run V o (StateT.run (match findInterval { s with prefixCuts := s.prefixCuts + 1 } i P 0 w with
    | none => if w ≤ 0 then pure (P.length, 0) else failP
    | some (k, w') =>
      if w' ≤ 0 then pure (k, (P.getD k default).a)
      else
        match findCell { s with prefixCuts := s.prefixCuts + 1 } i
            (({ s with prefixCuts := s.prefixCuts + 1 } : Rec ι).pts.filter
              (fun c => (P.getD k default).a ≤ c ∧ c < (P.getD k default).b) |>.sort (· ≤ ·)) w' with
        | none => failP
        | some (c, w'') => do
          let y ← cutQ i c w''
          if c < y ∧ y < ({ s with prefixCuts := s.prefixCuts + 1 } : Rec ι).nextPt c then
            splitCell N c y
          return (k, y)) { s with prefixCuts := s.prefixCuts + 1 }) tr₀ = _ at h
  have hpc : ∀ {m : Proto ι Pos}, Inv V PC0 m →
      Prog.run V o (m.run { s with prefixCuts := s.prefixCuts + 1 }) tr₀ = some ((p, s'), tr) →
      s'.prefixCuts = s.prefixCuts + 1 := fun hm hh => hm _ o tr₀ p s' tr hh
  split at h
  · split_ifs at h
    · exact hpc (inv_pure V PC0 pc0_refl _) h
    · exact hpc (inv_fail V PC0 pc0_refl) h
  · split_ifs at h
    · exact hpc (inv_pure V PC0 pc0_refl _) h
    · split at h
      · exact hpc (inv_fail V PC0 pc0_refl) h
      · refine hpc ?_ h
        refine inv_bind V PC0 pc0_refl pc0_trans (cut_pc0 V _ _ _) (fun y => ?_)
        dsimp only
        split_ifs
        · exact inv_bind V PC0 pc0_refl pc0_trans (split_pc0 V N _ _)
            (fun _ => inv_pure V PC0 pc0_refl _)
        · exact inv_pure V PC0 pc0_refl _


end


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


section main
variable {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)

theorem run_stbind {α β : Type} (o : ChoiceOracle ι) (m : Proto ι α) (f : α → Proto ι β)
    (t : Rec ι) (tr₀ : List (Event ι)) :
    Prog.run V o ((m >>= f).run t) tr₀ =
      match Prog.run V o (m.run t) tr₀ with
      | none => none
      | some ((x, t'), tr') => Prog.run V o ((f x).run t') tr' := by
  rw [StateT.run_bind]
  change Prog.run V o (Prog.bind (m.run t) (fun p => (f p.1).run p.2)) tr₀ = _
  rw [run_bind]
  rcases Prog.run V o (m.run t) tr₀ with _ | ⟨⟨x, t'⟩, tr'⟩ <;> rfl

theorem run_get' (o : ChoiceOracle ι) (t : Rec ι) (tr₀ : List (Event ι)) :
    Prog.run V o ((get : Proto ι (Rec ι)).run t) tr₀ = some ((t, t), tr₀) := rfl

theorem run_pure' {α : Type} (o : ChoiceOracle ι) (x : α) (t : Rec ι) (tr₀ : List (Event ι)) :
    Prog.run V o ((pure x : Proto ι α).run t) tr₀ = some ((x, t), tr₀) := rfl

theorem run_choose' {β : Type} (o : ChoiceOracle ι) (b : β) (bs : List β) (t : Rec ι)
    (tr₀ : List (Event ι)) :
    Prog.run V o ((chooseP (b :: bs) : Proto ι β).run t) tr₀ =
      some ((((b :: bs).get (o tr₀ bs.length)), t),
        tr₀ ++ [Event.choice bs.length (o tr₀ bs.length)]) := rfl

theorem run_shift {α : Type} (o : ChoiceOracle ι)
    (p : Prog ι α) (pretr tr : List (Event ι)) :
    Prog.run V o p (pretr ++ tr) =
      (Prog.run V (fun t m ↦ o (pretr ++ t) m) p tr).map
        (fun r : α × List (Event ι) ↦ (r.1, pretr ++ r.2)) := by
  induction p generalizing tr with
  | ret x => rfl
  | fail => rfl
  | eval i a b k ih =>
      simpa only [Prog.run, List.append_assoc] using
        ih (evalAnswer V i a b) (tr ++ [Event.eval i a b (evalAnswer V i a b)])
  | cut i x w k ih =>
      simpa only [Prog.run, List.append_assoc] using
        ih (cutAnswer V i x w) (tr ++ [Event.cut i x w (cutAnswer V i x w)])
  | choose m k ih =>
      simpa only [Prog.run, List.append_assoc] using
        ih (o (pretr ++ tr) m) (tr ++ [Event.choice m (o (pretr ++ tr) m)])

/-- Every trimming run succeeds, keeps the records valid, and makes at most one prefix cut per
earlier agent. -/
theorem trim_ok (Y : ι → Piece) (hY : ∀ i ∈ N, (Y i).WF) : ∀ (earlier : List ι),
    (∀ i ∈ earlier, i ∈ N) →
    ∀ (Q R0 : Piece) (t : Rec ι) (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
      Q.WF → t.Valid V N → (∀ i ∈ N, t.Aligned (Y i)) → t.Aligned Q →
      ∃ (B rem : Piece) (t' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((trimAgainst N Y earlier Q R0).run t) tr₀ = some (((B, rem), t'), tr) ∧
        t'.Valid V N ∧ t.pts ⊆ t'.pts ∧ B.WF ∧ t'.Aligned B ∧
        t'.prefixCuts ≤ t.prefixCuts + earlier.length := by
  intro earlier
  induction earlier with
  | nil =>
    intro _ Q R0 t o tr₀ hQ ht _ hQt
    exact ⟨Q, R0, t, tr₀, rfl, ht, subset_rfl, hQ, hQt, by simp⟩
  | cons a rest ih =>
    intro hear Q R0 t o tr₀ hQ ht hYt hQt
    have haN : a ∈ N := hear a (List.mem_cons_self ..)
    have hrest : ∀ i ∈ rest, i ∈ N := fun i hi => hear i (List.mem_cons_of_mem _ hi)
    simp only [trimAgainst, StateT.run_bind, StateT.run_get]
    change ∃ B rem t' tr, Prog.run V o (StateT.run (if 0 < t.pieceVal a Q - t.pieceVal a (Y a) then
          (do let p ← prefixCut N a Q (t.pieceVal a Q - t.pieceVal a (Y a))
              trimAgainst N Y rest (suffixList Q p) (R0 ++ prefixList Q p))
        else trimAgainst N Y rest Q R0) t) tr₀ = _ ∧ _
    split_ifs with hpos
    · have hvQ := recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
        V N t ht a haN Q hQ hQt
      have hvA := recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
        V N t ht a haN (Y a) (hY a haN) (hYt a haN)
      obtain ⟨p, t1, tr1, hpc, ht1, hsub, hvp, -, hsal, -, -⟩ :=
        prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1 V N a haN Q hQ t ht
          hQt (t.pieceVal a Q - t.pieceVal a (Y a)) hpos.le
          (by rw [hvQ, hvA]; linarith [value_nonneg (V a) (Y a)]) o tr₀
      have hpc1 := prefixCut_pc V N a Q _ t o tr₀ p t1 tr1 hpc
      have hswf : (suffixList Q p).WF := by
        rcases hvp with rfl | hvp
        · simp [suffixList, Piece.WF]
        · exact (cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1 Q hQ p hvp).2.1
      obtain ⟨B, rem, t', tr, hr, h1, h2, h3, h4, h5⟩ := ih hrest (suffixList Q p)
        (R0 ++ prefixList Q p) t1 o tr1 hswf ht1
        (fun i hi => aligned_mono t t1 hsub _ (hYt i hi)) hsal
      refine ⟨B, rem, t', tr, ?_, h1, hsub.trans h2, h3, h4, ?_⟩
      · rw [run_stbind, hpc]; exact hr
      · simp only [List.length_cons]; omega
    · obtain ⟨B, rem, t', tr, hr, h1, h2, h3, h4, h5⟩ := ih hrest Q R0 t o tr₀ hQ ht hYt hQt
      exact ⟨B, rem, t', tr, hr, h1, h2, h3, h4, by simp only [List.length_cons]; omega⟩

/-- Every candidate-loop run succeeds. -/
theorem cand_ok (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF) : ∀ (pairs : List (ι × ι)),
    (∀ q ∈ pairs, q.1 ∈ N ∧ q.2 ∈ N) →
    ∀ (earlier : List ι) (Y0 : ι → Piece) (R0 : Piece) (t : Rec ι) (o : ChoiceOracle ι)
      (tr₀ : List (Event ι)),
      (∀ i ∈ earlier, i ∈ N) → t.Valid V N → (∀ i ∈ N, t.Aligned (P i)) →
      (∀ i ∈ N, (Y0 i).WF ∧ t.Aligned (Y0 i)) →
      ∃ (Y : ι → Piece) (R : Piece) (t' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((candidateLoop N P pairs earlier Y0 R0).run t) tr₀ =
          some (((Y, R), t'), tr) ∧
        t'.Valid V N ∧ t.pts ⊆ t'.pts ∧ (∀ i ∈ N, (Y i).WF ∧ t'.Aligned (Y i)) ∧
        t'.prefixCuts ≤ t.prefixCuts + ∑ r ∈ Finset.range pairs.length, (earlier.length + r) := by
  intro pairs
  induction pairs with
  | nil =>
    intro _ earlier Y0 R0 t o tr₀ _ ht _ hY0
    exact ⟨Y0, R0, t, tr₀, rfl, ht, subset_rfl, hY0, by simp⟩
  | cons q rest ih =>
    obtain ⟨i, j⟩ := q
    intro hq earlier Y0 R0 t o tr₀ hear ht hPt hY0
    have hiN := (hq (i, j) (List.mem_cons_self ..)).1
    have hjN := (hq (i, j) (List.mem_cons_self ..)).2
    obtain ⟨B, rem, t1, tr1, hr1, ht1, hsub1, hBwf, hBal, hpc1⟩ :=
      trim_ok V N Y0 (fun k hk => (hY0 k hk).1) earlier hear (P j) [] t o tr₀ (hP j hjN) ht
        (fun k hk => (hY0 k hk).2) (hPt j hjN)
    obtain ⟨Y, R, t', tr, hr, h1, h2, h3, h4⟩ := ih (fun q hq' => hq q (List.mem_cons_of_mem _ hq'))
      (earlier ++ [i]) (Function.update Y0 i B) (R0 ++ rem) t1 o tr1
      (by intro k hk; rw [List.mem_append] at hk; rcases hk with hk | hk
          · exact hear k hk
          · simp at hk; exact hk ▸ hiN)
      ht1 (fun k hk => aligned_mono t t1 hsub1 _ (hPt k hk))
      (by intro k hk
          by_cases hki : k = i
          · subst hki; simp [hBwf, hBal]
          · rw [Function.update_of_ne hki]
            exact ⟨(hY0 k hk).1, aligned_mono t t1 hsub1 _ (hY0 k hk).2⟩)
    refine ⟨Y, R, t', tr, ?_, h1, hsub1.trans h2, h3, ?_⟩
    · simp only [candidateLoop]
      rw [run_stbind, hr1]
      exact hr
    · simp only [List.length_cons, List.length_append, List.length_nil, zero_add] at h4 ⊢
      rw [Finset.sum_range_succ']
      have : ∑ r ∈ Finset.range rest.length, (earlier.length + 1 + r) =
          ∑ r ∈ Finset.range rest.length, (earlier.length + (r + 1)) :=
        Finset.sum_congr rfl (fun r _ => by omega)
      omega

theorem sum_range_id' (n : ℕ) : ∑ r ∈ Finset.range n, (0 + r) = n.choose 2 := by
  simp only [zero_add]
  rw [Finset.sum_range_id, Nat.choose_two_right]

theorem guess_facts (g : List ι × List ι) (hg : g ∈ guesses N) :
    (∀ q ∈ g.1.zip g.2, q.1 ∈ N ∧ q.2 ∈ N) ∧ (g.1.zip g.2).length = N.card := by
  obtain ⟨l1, l2⟩ := g
  unfold guesses at hg
  rw [List.pair_mem_product, List.mem_permutations, List.mem_permutations] at hg
  obtain ⟨h1, h2⟩ := hg
  refine ⟨fun q hq => ?_, ?_⟩
  · have := List.of_mem_zip hq
    exact ⟨by rw [← Finset.mem_toList, ← h1.mem_iff]; exact this.1,
      by rw [← Finset.mem_toList, ← h2.mem_iff]; exact this.2⟩
  · simp only [List.length_zip, h1.length_eq, h2.length_eq, Finset.length_toList, min_self]

theorem guesses_length : (guesses N).length = (N.card.factorial) ^ 2 := by
  unfold guesses
  change (N.toList.permutations ×ˢ N.toList.permutations).length = _
  rw [List.length_product, List.length_permutations, Finset.length_toList, sq]

theorem rec_ef_iff (t : Rec ι) (ht : t.Valid V N) (Y : ι → Piece)
    (hY : ∀ i ∈ N, (Y i).WF ∧ t.Aligned (Y i)) :
    recEnvyFree t N Y ↔ EnvyFree V N (fun i ↦ (Y i).toSet) := by
  unfold recEnvyFree EnvyFree
  have hv : ∀ i ∈ N, ∀ j ∈ N, t.pieceVal i (Y j) = (V i).value (Y j).toSet := fun i hi j hj =>
    recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 V N t ht i hi (Y j)
      (hY j hj).1 (hY j hj).2
  constructor
  · intro h i hi j hj; rw [← hv i hi j hj, ← hv i hi i hi]; exact h i hi j hj
  · intro h i hi j hj; rw [hv i hi j hj, hv i hi i hi]; exact h i hi j hj

end main

end PSCAux

open PSCAux in
theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : N.Nonempty) (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (hgood : ∃ g ∈ guesses N,
      ∀ (t : Rec ι), t.Valid V N → (∀ i ∈ N, t.Aligned (P i)) →
        ∀ q : ChoiceOracle ι,
          ∃ (Y : ι → Piece) (R : Piece) (u : Rec ι) (tr : List (Event ι)),
            exec V q (candidate N P g.1 g.2) t = some ((Y, R), u, tr) ∧
            EnvyFree V N (fun i ↦ (Y i).toSet))
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (o : ChoiceOracle ι) :
    ∃ (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (permute N P) s = some ((Y, R), s', tr) ∧
      EnvyFree V N (fun i ↦ (Y i).toSet) ∧
      s'.prefixCuts ≤ s.prefixCuts + N.card.choose 2 * (N.card.factorial) ^ 2 ∧
      ∃ (g : List ι × List ι) (t : Rec ι) (q : ChoiceOracle ι)
        (tc : List (Event ι)),
        g ∈ guesses N ∧ t.Valid V N ∧ (∀ i ∈ N, t.Aligned (P i)) ∧
        exec V q (candidate N P g.1 g.2) t = some ((Y, R), s', tc) := by
  obtain ⟨gs0, hgs0, hgood⟩ := hgood
  set c := N.card.choose 2 with hc
  -- a successful candidate run, from any valid aligned state
  have candRun : ∀ (g : List ι × List ι), g ∈ guesses N → ∀ (t : Rec ι) (o : ChoiceOracle ι)
      (tr₀ : List (Event ι)), t.Valid V N → (∀ i ∈ N, t.Aligned (P i)) →
      ∃ (Y : ι → Piece) (R : Piece) (t' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((candidate N P g.1 g.2).run t) tr₀ = some (((Y, R), t'), tr) ∧
        t'.Valid V N ∧ t.pts ⊆ t'.pts ∧ (∀ i ∈ N, (Y i).WF ∧ t'.Aligned (Y i)) ∧
        t'.prefixCuts ≤ t.prefixCuts + c := by
    intro g hg t o tr₀ ht hPt
    obtain ⟨hq, hlen⟩ := guess_facts N g hg
    obtain ⟨Y, R, t', tr, hr, h1, h2, h3, h4⟩ := cand_ok V N P hP (g.1.zip g.2) hq [] (fun _ => [])
      [] t o tr₀ (by simp) ht hPt (by intro i _; simp [Piece.WF, Rec.Aligned])
    refine ⟨Y, R, t', tr, hr, h1, h2, h3, ?_⟩
    rw [hlen, List.length_nil, sum_range_id'] at h4; exact h4
  -- the search loop
  have loop : ∀ (k : ℕ) (gs : List (List ι × List ι)) (t : Rec ι) (o : ChoiceOracle ι)
      (tr₀ : List (Event ι)), gs0 ∈ gs → gs.length ≤ k → (∀ g ∈ gs, g ∈ guesses N) →
      t.Valid V N → (∀ i ∈ N, t.Aligned (P i)) →
      ∃ (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((permuteLoop N P k gs).run t) tr₀ = some (((Y, R), s'), tr) ∧
        EnvyFree V N (fun i ↦ (Y i).toSet) ∧
        s'.prefixCuts ≤ t.prefixCuts + c * gs.length ∧
        ∃ (g : List ι × List ι) (t₁ : Rec ι) (q : ChoiceOracle ι) (tc : List (Event ι)),
          g ∈ guesses N ∧ t₁.Valid V N ∧ (∀ i ∈ N, t₁.Aligned (P i)) ∧
          exec V q (candidate N P g.1 g.2) t₁ = some ((Y, R), s', tc) := by
    classical
    intro k
    induction k with
    | zero =>
      intro gs t o tr₀ hmem hlen
      have := List.length_pos_of_mem hmem; omega
    | succ k ih =>
      intro gs t o tr₀ hmem hlen hgs ht hPt
      obtain ⟨b, bs, rfl⟩ : ∃ b bs, gs = b :: bs := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
      set g := (b :: bs).get (o tr₀ bs.length) with hgdef
      set tr1 := tr₀ ++ [Event.choice bs.length (o tr₀ bs.length)] with htr1
      have hgmem : g ∈ b :: bs := List.get_mem _ _
      have hgG : g ∈ guesses N := hgs g hgmem
      obtain ⟨Y, R, t1, tr2, hr, ht1, hsub, hY, hpc⟩ := candRun g hgG t o tr1 ht hPt
      -- the shifted oracle and transcript of the candidate run
      have hshift := run_shift V o ((candidate N P g.1 g.2).run t) tr1 []
      rw [List.append_nil, hr] at hshift
      rcases hq : Prog.run V (fun t' m ↦ o (tr1 ++ t') m) ((candidate N P g.1 g.2).run t) [] with
        _ | ⟨⟨⟨Y', R'⟩, t1'⟩, tc⟩
      · rw [hq] at hshift; simp at hshift
      rw [hq] at hshift
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hshift
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, htc⟩ := hshift
      have hexec : exec V (fun t' m ↦ o (tr1 ++ t') m) (candidate N P g.1 g.2) t =
          some ((Y, R), t1, tc) := by unfold exec; rw [hq]
      have hunfold : Prog.run V o ((permuteLoop N P (k + 1) (b :: bs)).run t) tr₀ =
          Prog.run V o ((if recEnvyFree t1 N Y then (pure (Y, R) : Proto ι _)
            else permuteLoop N P k ((b :: bs).erase g)).run t1) tr2 := by
        simp only [permuteLoop]
        rw [run_stbind, run_choose']
        dsimp only
        rw [← hgdef, ← htr1, run_stbind, hr]
        dsimp only
        rw [run_stbind, run_get']
      by_cases hef : recEnvyFree t1 N Y
      · refine ⟨Y, R, t1, tr2, ?_, (rec_ef_iff V N t1 ht1 Y hY).1 hef, ?_,
          g, t, _, tc, hgG, ht, hPt, hexec⟩
        · rw [hunfold, if_pos hef, run_pure']
        · have : c ≤ c * (b :: bs).length := Nat.le_mul_of_pos_right _ (by simp)
          omega
      · have hne : g ≠ gs0 := by
          rintro rfl
          obtain ⟨Y'', R'', u, tr', he, hEF⟩ := hgood t ht hPt (fun t' m ↦ o (tr1 ++ t') m)
          rw [hexec] at he
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨⟨rfl, -⟩, -⟩ := he
          exact hef ((rec_ef_iff V N t1 ht1 Y hY).2 hEF)
        have hmem' : gs0 ∈ (b :: bs).erase g := (List.mem_erase_of_ne (Ne.symm hne)).2 hmem
        have hlen' : ((b :: bs).erase g).length = bs.length := by
          rw [List.length_erase_of_mem hgmem]; simp
        obtain ⟨Y2, R2, s2, tr3, hr3, hEF2, hpc2, wit⟩ := ih ((b :: bs).erase g) t1 o tr2 hmem'
          (by rw [hlen']; simp at hlen; omega)
          (fun g' hg' => hgs g' (List.mem_of_mem_erase hg')) ht1
          (fun i hi => aligned_mono t t1 hsub _ (hPt i hi))
        refine ⟨Y2, R2, s2, tr3, ?_, hEF2, ?_, wit⟩
        · rw [hunfold, if_neg hef]; exact hr3
        · rw [hlen'] at hpc2
          simp only [List.length_cons, Nat.mul_succ]
          omega
  obtain ⟨Y, R, s', tr, hr, hEF, hpc, wit⟩ := loop (guesses N).length (guesses N) s o []
    hgs0 le_rfl (fun g hg => hg) hs hPs
  refine ⟨Y, R, s', tr, ?_, hEF, ?_, wit⟩
  · unfold exec permute; rw [hr]
  · rw [guesses_length] at hpc; exact hpc
