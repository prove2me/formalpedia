-- Prove2me | solution 1 for EnvyFreeCake104.Divide.permute_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T17:18:27.344636+00:00
-- url     : https://prove2.me/submissions/b6e2c57c-a35d-4fff-93bd-12dd149fde6d

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
import Theorems.Thm_EnvyFreeCake104_Divide_cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
import Theorems.Thm_EnvyFreeCake104_Divide_recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2

import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_query_bound__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1
import Theorems.Thm_EnvyFreeCake104_Divide_splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2

open EnvyFreeCake104.Divide

namespace PIAux

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


theorem run_fail' {α : Type} (o : ChoiceOracle ι) (t : Rec ι) (tr₀ : List (Event ι)) :
    Prog.run V o ((failP : Proto ι α).run t) tr₀ = none := rfl

theorem wf_append (A B : Piece) (hA : A.WF) (hB : B.WF) (hd : Disjoint A.toSet B.toSet) :
    (A ++ B).WF := by
  refine ⟨fun I hI => ?_, ?_⟩
  · rcases List.mem_append.mp hI with h | h
    · exact hA.1 I h
    · exact hB.1 I h
  · rw [List.pairwise_append]
    refine ⟨hA.2, hB.2, fun I hI J hJ => ?_⟩
    have hIA : I.toSet ⊆ A.toSet := fun x hx => (⟨I, hI, hx⟩ : ∃ K ∈ A, x ∈ K.toSet)
    have hJB : J.toSet ⊆ B.toSet := fun x hx => (⟨J, hJ, hx⟩ : ∃ K ∈ B, x ∈ K.toSet)
    exact Disjoint.mono hIA hJB hd

theorem aligned_append (t : Rec ι) (A B : Piece) (hA : t.Aligned A) (hB : t.Aligned B) :
    t.Aligned (A ++ B) := by
  intro I hI
  rcases List.mem_append.mp hI with h | h
  · exact hA I h
  · exact hB I h

theorem wf_nil : Piece.WF [] := ⟨by simp, by simp⟩

/-- Trimming: success, validity, and well-formedness of both outputs. -/
theorem trim2 (Y : ι → Piece) (hY : ∀ i ∈ N, (Y i).WF) : ∀ (earlier : List ι),
    (∀ i ∈ earlier, i ∈ N) →
    ∀ (Q R0 : Piece) (t : Rec ι) (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
      Q.WF → R0.WF → Disjoint Q.toSet R0.toSet →
      t.Valid V N → (∀ i ∈ N, t.Aligned (Y i)) → t.Aligned Q → t.Aligned R0 →
      ∃ (B rem : Piece) (t' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((trimAgainst N Y earlier Q R0).run t) tr₀ = some (((B, rem), t'), tr) ∧
        t'.Valid V N ∧ t.pts ⊆ t'.pts ∧ B.WF ∧ t'.Aligned B ∧ rem.WF ∧ t'.Aligned rem ∧
        Disjoint B.toSet rem.toSet ∧ B.toSet ∪ rem.toSet = Q.toSet ∪ R0.toSet := by
  intro earlier
  induction earlier with
  | nil =>
    intro _ Q R0 t o tr₀ hQ hR0 hd ht _ hQt hR0t
    exact ⟨Q, R0, t, tr₀, rfl, ht, subset_rfl, hQ, hQt, hR0, hR0t, hd, rfl⟩
  | cons a rest ih =>
    intro hear Q R0 t o tr₀ hQ hR0 hd ht hYt hQt hR0t
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
      obtain ⟨p, t1, tr1, hpc, ht1, hsub, hvp, hpal, hsal, -, -⟩ :=
        prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1 V N a haN Q hQ t ht
          hQt (t.pieceVal a Q - t.pieceVal a (Y a)) hpos.le
          (by rw [hvQ, hvA]; linarith [value_nonneg (V a) (Y a)]) o tr₀
      have hpart : (prefixList Q p).WF ∧ (suffixList Q p).WF ∧
          Disjoint (prefixList Q p).toSet (suffixList Q p).toSet ∧
          (prefixList Q p).toSet ∪ (suffixList Q p).toSet = Q.toSet := by
        rcases hvp with rfl | hvp
        · simp [prefixList, suffixList, Piece.WF, toSet_nil]
        · exact cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1 Q hQ p hvp
      obtain ⟨hpwf, hswf, hpsd, hpsu⟩ := hpart
      have hpQ : (prefixList Q p).toSet ⊆ Q.toSet := hpsu ▸ Set.subset_union_left
      have hsQ : (suffixList Q p).toSet ⊆ Q.toSet := hpsu ▸ Set.subset_union_right
      obtain ⟨B, rem, t', tr, hr, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih hrest (suffixList Q p)
        (R0 ++ prefixList Q p) t1 o tr1 hswf
        (wf_append _ _ hR0 hpwf (Disjoint.mono_left hpQ hd).symm)
        (by rw [toSet_append]
            exact Disjoint.union_right (Disjoint.mono_left hsQ hd) hpsd.symm)
        ht1 (fun i hi => aligned_mono t t1 hsub _ (hYt i hi)) hsal
        (aligned_append t1 _ _ (aligned_mono t t1 hsub _ hR0t) hpal)
      refine ⟨B, rem, t', tr, ?_, h1, hsub.trans h2, h3, h4, h5, h6, h7, ?_⟩
      · rw [run_stbind, hpc]; exact hr
      · rw [h8, toSet_append, ← hpsu]; ext x; simp only [Set.mem_union]; tauto
    · exact ih hrest Q R0 t o tr₀ hQ hR0 hd ht hYt hQt hR0t

/-- Candidate loop: success, validity, and well-formedness of bundles and residue. -/
theorem cand2 (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet) :
    ∀ (pairs : List (ι × ι)),
    (∀ q ∈ pairs, q.1 ∈ N ∧ q.2 ∈ N) → (pairs.map Prod.snd).Nodup →
    ∀ (earlier : List ι) (Y0 : ι → Piece) (R0 : Piece) (t : Rec ι) (o : ChoiceOracle ι)
      (tr₀ : List (Event ι)),
      (∀ i ∈ earlier, i ∈ N) → t.Valid V N → (∀ i ∈ N, t.Aligned (P i)) →
      (∀ i ∈ N, (Y0 i).WF ∧ t.Aligned (Y0 i)) → R0.WF → t.Aligned R0 →
      (∀ q ∈ pairs, Disjoint (P q.2).toSet R0.toSet) →
      ∃ (Y : ι → Piece) (R : Piece) (t' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((candidateLoop N P pairs earlier Y0 R0).run t) tr₀ =
          some (((Y, R), t'), tr) ∧
        t'.Valid V N ∧ t.pts ⊆ t'.pts ∧ (∀ i ∈ N, (Y i).WF ∧ t'.Aligned (Y i)) ∧
        R.WF ∧ t'.Aligned R := by
  intro pairs
  induction pairs with
  | nil =>
    intro _ _ earlier Y0 R0 t o tr₀ _ ht _ hY0 hR0 hR0t _
    exact ⟨Y0, R0, t, tr₀, rfl, ht, subset_rfl, hY0, hR0, hR0t⟩
  | cons q rest ih =>
    obtain ⟨i, j⟩ := q
    intro hq hnd earlier Y0 R0 t o tr₀ hear ht hPt hY0 hR0 hR0t hdR
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hiN := (hq (i, j) (List.mem_cons_self ..)).1
    have hjN := (hq (i, j) (List.mem_cons_self ..)).2
    obtain ⟨B, rem, t1, tr1, hr1, ht1, hsub1, hBwf, hBal, hremwf, hremal, -, hBrem⟩ :=
      trim2 V N Y0 (fun k hk => (hY0 k hk).1) earlier hear (P j) [] t o tr₀ (hP j hjN) wf_nil
        (by simp [toSet_nil]) ht (fun k hk => (hY0 k hk).2) (hPt j hjN) (by intro I hI; simp at hI)
    rw [toSet_nil, Set.union_empty] at hBrem
    have hremP : rem.toSet ⊆ (P j).toSet := hBrem ▸ Set.subset_union_right
    obtain ⟨Y, R, t', tr, hr, h1, h2, h3, h4, h5⟩ := ih (fun q hq' => hq q (List.mem_cons_of_mem _ hq'))
      hnd.2 (earlier ++ [i]) (Function.update Y0 i B) (R0 ++ rem) t1 o tr1
      (by intro k hk; rw [List.mem_append] at hk; rcases hk with hk | hk
          · exact hear k hk
          · simp at hk; exact hk ▸ hiN)
      ht1 (fun k hk => aligned_mono t t1 hsub1 _ (hPt k hk))
      (by intro k hk
          by_cases hki : k = i
          · subst hki; simp [hBwf, hBal]
          · rw [Function.update_of_ne hki]
            exact ⟨(hY0 k hk).1, aligned_mono t t1 hsub1 _ (hY0 k hk).2⟩)
      (wf_append _ _ hR0 hremwf (Disjoint.mono_right hremP (hdR (i, j) (List.mem_cons_self ..)).symm))
      (aligned_append t1 _ _ (aligned_mono t t1 hsub1 _ hR0t) hremal)
      (by intro q hq'
          have hqN := (hq q (List.mem_cons_of_mem _ hq')).2
          have hqj : q.2 ≠ j := by rintro h; exact hnd.1 ⟨q, hq', h⟩
          rw [toSet_append]
          exact Disjoint.union_right (hdR q (List.mem_cons_of_mem _ hq'))
            (Disjoint.mono_right hremP (hPdisj q.2 hqN j hjN hqj)))
    refine ⟨Y, R, t', tr, ?_, h1, hsub1.trans h2, h3, h4, h5⟩
    simp only [candidateLoop]
    rw [run_stbind, hr1]
    exact hr

theorem guess_snd_nodup (g : List ι × List ι) (hg : g ∈ guesses N) :
    ((g.1.zip g.2).map Prod.snd).Nodup := by
  obtain ⟨l1, l2⟩ := g
  unfold guesses at hg
  rw [List.pair_mem_product, List.mem_permutations, List.mem_permutations] at hg
  obtain ⟨h1, h2⟩ := hg
  rw [List.map_snd_zip (by rw [h1.length_eq, h2.length_eq])]
  exact h2.nodup_iff.mpr (Finset.nodup_toList N)

end main

end PIAux

open PIAux in
theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (o : ChoiceOracle ι) (tr₀ : List (Event ι))
    (Y : ι → Piece) (U : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : Prog.run V o ((permute N P).run s) tr₀ = some (((Y, U), s'), tr)) :
    s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ (∀ i ∈ N, (Y i).WF ∧ s'.Aligned (Y i)) ∧
      U.WF ∧ s'.Aligned U := by
  classical
  have key : ∀ (k : ℕ) (gs : List (List ι × List ι)) (t : Rec ι) (o : ChoiceOracle ι)
      (tr₀ : List (Event ι)) (Y : ι → Piece) (U : Piece) (t' : Rec ι) (tr : List (Event ι)),
      (∀ g ∈ gs, g ∈ guesses N) → t.Valid V N → (∀ i ∈ N, t.Aligned (P i)) →
      Prog.run V o ((permuteLoop N P k gs).run t) tr₀ = some (((Y, U), t'), tr) →
      t'.Valid V N ∧ t.pts ⊆ t'.pts ∧ (∀ i ∈ N, (Y i).WF ∧ t'.Aligned (Y i)) ∧
        U.WF ∧ t'.Aligned U := by
    intro k
    induction k with
    | zero =>
      intro gs t o tr₀ Y U t' tr _ _ _ h
      rw [permuteLoop, run_fail'] at h; exact absurd h (by simp)
    | succ k ih =>
      intro gs t o tr₀ Y U t' tr hgs ht hPt h
      cases gs with
      | nil =>
        simp only [permuteLoop] at h
        rw [run_stbind] at h
        simp [chooseP, run_fail'] at h
      | cons b bs =>
        simp only [permuteLoop] at h
        rw [run_stbind, run_choose'] at h
        dsimp only at h
        set g := (b :: bs).get (o tr₀ bs.length)
        have hgG : g ∈ guesses N := hgs g (List.get_mem _ _)
        obtain ⟨hq, -⟩ := guess_facts N g hgG
        obtain ⟨Y1, R1, t1, tr1, hr1, h1, h2, h3, h4, h5⟩ := cand2 V N P hP hPdisj (g.1.zip g.2) hq
          (guess_snd_nodup N g hgG) [] (fun _ => []) [] t o _ (by simp) ht hPt
          (by intro i _; simp [Piece.WF, Rec.Aligned]) wf_nil (by intro I hI; simp at hI)
          (by intro q _; simp [toSet_nil])
        rw [run_stbind] at h
        unfold candidate at h
        rw [hr1] at h
        dsimp only at h
        rw [run_stbind, run_get'] at h
        dsimp only at h
        split_ifs at h
        · rw [run_pure'] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
          exact ⟨h1, h2, h3, h4, h5⟩
        · obtain ⟨g1, g2, g3, g4, g5⟩ := ih _ t1 o _ Y U t' tr
            (fun g' hg' => hgs g' (List.mem_of_mem_erase hg')) h1
            (fun i hi => aligned_mono t t1 h2 _ (hPt i hi)) h
          exact ⟨g1, h2.trans g2, g3, g4, g5⟩
  exact key _ _ s o tr₀ Y U s' tr (fun g hg => hg) hs hPs hrun
