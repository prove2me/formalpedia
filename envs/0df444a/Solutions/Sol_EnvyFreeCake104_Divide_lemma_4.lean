-- Prove2me | solution 1 for EnvyFreeCake104.Divide.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T18:19:49.945184+00:00
-- url     : https://prove2.me/submissions/69ddc575-a21f-4909-ae53-ba5ce1935f04

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_query_bound__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1
import Theorems.Thm_EnvyFreeCake104_Divide_splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
import Theorems.Thm_EnvyFreeCake104_Divide_recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
import Theorems.Thm_EnvyFreeCake104_Divide_lemma_6
import Theorems.Thm_EnvyFreeCake104_Divide_permute_query_meter__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2
open EnvyFreeCake104.Divide
namespace L4Aux

theorem interval_measurable (I : Interval) : MeasurableSet I.toSet := by
  unfold Interval.toSet; split_ifs
  · exact measurableSet_Icc
  · exact measurableSet_Ico

theorem piece_measurable (P : Piece) : MeasurableSet P.toSet := by
  have : P.toSet = ⋃ I ∈ P, I.toSet := by ext x; simp [Piece.toSet]
  rw [this]
  exact MeasurableSet.biUnion P.finite_toSet.countable (fun I _ => interval_measurable I)

theorem value_mono (v : Valuation) {A B : Set ℝ} (h : A ⊆ B) (hB : MeasurableSet B) :
    v.value A ≤ v.value B := by
  unfold Valuation.value
  apply MeasureTheory.setIntegral_mono_set (v.integrable.mono_set Set.inter_subset_right)
  · exact MeasureTheory.ae_restrict_of_forall_mem (hB.inter measurableSet_Icc)
      (fun x hx => v.nonneg x hx.2)
  · exact (Set.inter_subset_inter_left _ h).eventuallyLE

theorem value_union (v : Valuation) {A B : Set ℝ} (hB : MeasurableSet B) (hd : Disjoint A B) :
    v.value (A ∪ B) = v.value A + v.value B := by
  unfold Valuation.value
  rw [Set.union_inter_distrib_right]
  apply MeasureTheory.setIntegral_union
  · exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left hd
  · exact hB.inter measurableSet_Icc
  · exact v.integrable.mono_set Set.inter_subset_right
  · exact v.integrable.mono_set Set.inter_subset_right

theorem value_empty (v : Valuation) : v.value ∅ = 0 := by simp [Valuation.value]

theorem value_nonneg (v : Valuation) {A : Set ℝ} (hA : MeasurableSet A) : 0 ≤ v.value A := by
  have := value_mono v (Set.empty_subset A) hA
  rwa [value_empty] at this

theorem value_biUnion {ι : Type} [DecidableEq ι] (v : Valuation) (A : ι → Set ℝ) (s : Finset ι)
    (hm : ∀ i ∈ s, MeasurableSet (A i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)) :
    v.value (⋃ i ∈ s, A i) = ∑ i ∈ s, v.value (A i) := by
  induction s using Finset.induction_on with
  | empty => simp [value_empty]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    have hms : MeasurableSet (⋃ i ∈ s, A i) :=
      Finset.measurableSet_biUnion s (fun i hi => hm i (Finset.mem_insert_of_mem hi))
    rw [value_union v hms, ih (fun i hi => hm i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hij => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)]
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨j, hj, hxj⟩ := hx'
    exact Set.disjoint_left.mp (hd a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
      (fun h => ha (h ▸ hj))) hx hxj
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

theorem run_stbind {ι α β : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (m : Proto ι α)
    (f : α → Proto ι β) (t : Rec ι) (tr₀ : List (Event ι)) :
    Prog.run V o ((m >>= f).run t) tr₀ =
      match Prog.run V o (m.run t) tr₀ with
      | none => none
      | some ((x, t'), tr') => Prog.run V o ((f x).run t') tr' := by
  rw [StateT.run_bind]
  change Prog.run V o (Prog.bind (m.run t) (fun p => (f p.1).run p.2)) tr₀ = _
  rw [run_bind]
  rcases Prog.run V o (m.run t) tr₀ with _ | ⟨⟨x, t'⟩, tr'⟩ <;> rfl

theorem run_get' {ι : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (t : Rec ι)
    (tr₀ : List (Event ι)) :
    Prog.run V o ((get : Proto ι (Rec ι)).run t) tr₀ = some ((t, t), tr₀) := rfl

theorem run_pure' {ι α : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (x : α) (t : Rec ι)
    (tr₀ : List (Event ι)) :
    Prog.run V o ((pure x : Proto ι α).run t) tr₀ = some ((x, t), tr₀) := rfl

theorem run_fail' {ι α : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (t : Rec ι)
    (tr₀ : List (Event ι)) :
    Prog.run V o ((failP : Proto ι α).run t) tr₀ = none := rfl

theorem run_choose_cons {ι β : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (b : β)
    (bs : List β) (t : Rec ι) (tr₀ : List (Event ι)) :
    Prog.run V o ((chooseP (b :: bs) : Proto ι β).run t) tr₀ =
      some ((((b :: bs).get (o tr₀ bs.length)), t),
        tr₀ ++ [Event.choice bs.length (o tr₀ bs.length)]) := rfl

theorem run_choose_ex {ι β : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (l : List β)
    (hl : l ≠ []) (t : Rec ι) (tr₀ : List (Event ι)) :
    ∃ x ∈ l, ∃ tr, Prog.run V o ((chooseP l : Proto ι β).run t) tr₀ = some ((x, t), tr) ∧
      queryCount tr = queryCount tr₀ := by
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hl
  exact ⟨_, List.get_mem _ _, _, run_choose_cons V o b bs t tr₀,
    by simp [queryCount, List.countP_append, Event.isQuery]⟩

theorem run_shift {ι α : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
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

theorem exec_iff {ι α : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (p : Proto ι α) (s : Rec ι) (x : α) (s' : Rec ι) (tr : List (Event ι)) :
    exec V o p s = some (x, s', tr) ↔ Prog.run V o (p.run s) [] = some ((x, s'), tr) := by
  unfold exec
  rcases Prog.run V o (p.run s) [] with _ | ⟨⟨u, t⟩, l⟩
  · simp
  · simp only [Option.some.injEq, Prod.mk.injEq, and_assoc]

/-- Running from a nonempty transcript: shift the oracle. -/
theorem run_from_exec {ι α : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (p : Proto ι α)
    (s : Rec ι) (tr₁ : List (Event ι)) (x : α) (s' : Rec ι) (tc : List (Event ι))
    (h : exec V (fun t m ↦ o (tr₁ ++ t) m) p s = some (x, s', tc)) :
    Prog.run V o (p.run s) tr₁ = some ((x, s'), tr₁ ++ tc) := by
  have := run_shift V o (p.run s) tr₁ []
  rw [List.append_nil] at this
  rw [this, (exec_iff V _ p s x s' tc).mp h]
  rfl

theorem toSet_append (A B : Piece) : Piece.toSet (A ++ B) = A.toSet ∪ B.toSet := by
  ext x; simp [Piece.toSet, or_and_right, exists_or]

theorem toSet_nil : Piece.toSet [] = ∅ := by
  ext x; simp [Piece.toSet]

theorem aligned_mono {ι : Type} (s t : Rec ι) (h : s.pts ⊆ t.pts) (P : Piece)
    (hP : s.Aligned P) : t.Aligned P := fun I hI => ⟨h (hP I hI).1, h (hP I hI).2⟩

theorem valid_mono {ι : Type} (V : ι → Valuation) (N E : Finset ι) (s : Rec ι)
    (hs : s.Valid V N) (hE : E ⊆ N) : s.Valid V E :=
  ⟨hs.1, hs.2.1, hs.2.2.1, fun i hi => hs.2.2.2 i (hE hi)⟩

/-- Refinement of protocols: every successful run of `m` is a successful run of `m'`. -/
def PRef {ι α : Type} (V : ι → Valuation) (m m' : Proto ι α) : Prop :=
  ∀ (s : Rec ι) (o : ChoiceOracle ι) (tr : List (Event ι)) r,
    Prog.run V o (m.run s) tr = some r → Prog.run V o (m'.run s) tr = some r

theorem pref_refl {ι α : Type} (V : ι → Valuation) (m : Proto ι α) : PRef V m m :=
  fun _ _ _ _ h => h

theorem pref_bind {ι α β : Type} (V : ι → Valuation) {m m' : Proto ι α}
    {f f' : α → Proto ι β} (hm : PRef V m m') (hf : ∀ x, PRef V (f x) (f' x)) :
    PRef V (m >>= f) (m' >>= f') := by
  intro s o tr r h
  rw [run_stbind] at h ⊢
  rcases h1 : Prog.run V o (m.run s) tr with _ | ⟨⟨x, t⟩, tr'⟩
  · rw [h1] at h; simp at h
  · rw [h1] at h; rw [hm s o tr _ h1]; exact hf x t o tr' r h
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

theorem aligned_append {ι : Type} (t : Rec ι) (A B : Piece) (hA : t.Aligned A)
    (hB : t.Aligned B) : t.Aligned (A ++ B) := by
  intro I hI
  rcases List.mem_append.mp hI with h | h
  · exact hA I h
  · exact hB I h

theorem wf_nil : Piece.WF [] := ⟨by simp, by simp⟩
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
theorem choose_state {ι β : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (l : List β)
    (t : Rec ι) (tr₀ : List (Event ι)) (x : β) (t' : Rec ι) (tr : List (Event ι))
    (h : Prog.run V o ((chooseP l : Proto ι β).run t) tr₀ = some ((x, t'), tr)) :
    t' = t ∧ x ∈ l := by
  cases l with
  | nil => simp [chooseP, run_fail'] at h
  | cons b bs =>
    rw [run_choose_cons] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    exact ⟨rfl, List.get_mem _ _⟩

theorem value_union_le (v : Valuation) {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) : v.value (A ∪ B) ≤ v.value A + v.value B := by
  have : A ∪ B = A ∪ (B \ A) := by ext x; simp only [Set.mem_union, Set.mem_sdiff]; tauto
  rw [this, value_union v (hB.diff hA) Set.disjoint_sdiff_right]
  linarith [value_mono v (Set.sdiff_subset : B \ A ⊆ B) hB]

theorem value_sdiff (v : Valuation) {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : B ⊆ A) : v.value (A \ B) = v.value A - v.value B := by
  have hA' : A = (A \ B) ∪ B := (Set.sdiff_union_of_subset h).symm
  have := value_union v hB (Set.disjoint_sdiff_left : Disjoint (A \ B) B)
  rw [← hA'] at this; linarith

theorem ivl_mono {x x' b : ℝ} (h : x' ≤ x) :
    Interval.toSet ⟨x, b⟩ ⊆ Interval.toSet ⟨x', b⟩ := by
  intro y hy
  simp only [Interval.toSet] at hy ⊢
  split_ifs at hy with h1 <;> split_ifs with h2
  · exact ⟨le_trans h hy.1, hy.2⟩
  · exact absurd ⟨h1.1, lt_of_le_of_lt h h1.2⟩ h2
  · exact ⟨le_trans h hy.1, hy.2.le⟩
  · exact ⟨le_trans h hy.1, hy.2⟩

theorem suffix_sub_piece (P : Piece) (S : Set ℝ) (h : IsSuffix S P) : S ⊆ P.toSet := by
  rcases h with rfl | ⟨⟨k, x⟩, ⟨hk, hxa, hxb⟩, rfl⟩
  · exact Set.empty_subset _
  · simp only at hk hxa hxb
    intro y hy
    simp only [suffixList, if_pos hk] at hy
    obtain ⟨I, hI, hyI⟩ := hy
    rcases List.mem_cons.mp hI with rfl | hI
    · refine ⟨P.getD k default, ?_, ?_⟩
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem _
      · have := ivl_mono (b := (P.getD k default).b) hxa hyI
        simpa using this
    · exact ⟨I, List.mem_of_mem_drop hI, hyI⟩

/-- A suffix of `A ++ B` either contains `B` or is a suffix of `B`. -/
theorem suffix_append (A B : Piece) (S : Set ℝ) (h : IsSuffix S (A ++ B)) :
    B.toSet ⊆ S ∨ IsSuffix S B := by
  rcases h with rfl | ⟨⟨k, x⟩, ⟨hk, hxa, hxb⟩, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · simp only at hk hxa hxb
    by_cases hkA : k < A.length
    · left
      intro y hy
      obtain ⟨J, hJ, hyJ⟩ := hy
      simp only [suffixList, if_pos hk]
      refine ⟨J, List.mem_cons_of_mem _ ?_, hyJ⟩
      rw [List.drop_append_of_le_length (by omega)]
      exact List.mem_append_right _ hJ
    · right
      have hkB : k - A.length < B.length := by simp at hk; omega
      have hget : (A ++ B).getD k default = B.getD (k - A.length) default := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by omega)]
      refine Or.inr ⟨(k - A.length, x), ⟨hkB, by rw [← hget]; exact hxa,
        by rw [← hget]; exact hxb⟩, ?_⟩
      simp only [suffixList, if_pos hk, if_pos hkB, hget]
      congr 2
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
      congr 1; omega

theorem toSet_flatten (BL : List Piece) :
    Piece.toSet BL.flatten = ⋃ b ∈ Finset.range BL.length, (BL.getD b []).toSet := by
  ext y
  simp only [Piece.toSet, Set.mem_setOf_eq, List.mem_flatten, Set.mem_iUnion, Finset.mem_range,
    exists_prop]
  constructor
  · rintro ⟨I, ⟨B, hB, hIB⟩, hy⟩
    obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hB
    exact ⟨b, hb, I, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]; exact hIB, hy⟩
  · rintro ⟨b, hb, I, hI, hy⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb] at hI
    exact ⟨I, ⟨_, List.getElem_mem hb, hI⟩, hy⟩

/-- Suffixes of a concatenation of blocks: if block `b` is not contained in the suffix, the suffix
lies in blocks `b, b+1, …`. -/
theorem suffix_blocks : ∀ (BL : List Piece) (S : Set ℝ), IsSuffix S BL.flatten →
    ∀ b < BL.length, ¬ ((BL.getD b []).toSet ⊆ S) →
    S ⊆ ⋃ b' ∈ Finset.Ico b BL.length, (BL.getD b' []).toSet := by
  intro BL
  induction BL with
  | nil => intro S _ b hb; simp at hb
  | cons B rest ih =>
    intro S hS b hb hnot
    rw [List.flatten_cons] at hS
    cases b with
    | zero =>
      have := suffix_sub_piece _ S hS
      rw [← List.flatten_cons, toSet_flatten] at this
      intro y hy
      obtain ⟨b', hb', hyb'⟩ := Set.mem_iUnion₂.mp (this hy)
      exact Set.mem_iUnion₂.mpr ⟨b', by simp at hb' ⊢; omega, hyb'⟩
    | succ b =>
      rcases suffix_append B rest.flatten S hS with hsub | hsuf
      · exfalso; apply hnot
        refine Set.Subset.trans ?_ hsub
        rw [toSet_flatten]
        intro y hy
        exact Set.mem_iUnion₂.mpr ⟨b, by simp at hb ⊢; omega, by simpa using hy⟩
      · have := ih S hsuf b (by simp at hb; omega) (by simpa using hnot)
        intro y hy
        obtain ⟨b', hb', hyb'⟩ := Set.mem_iUnion₂.mp (this hy)
        exact Set.mem_iUnion₂.mpr ⟨b' + 1, by simp at hb' ⊢; omega, by simpa using hyb'⟩
/-- Lexicographic order on positions. -/
def PLE (p q : Pos) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

theorem PLE_refl (p : Pos) : PLE p p := Or.inr ⟨rfl, le_rfl⟩

theorem PLE_trans {p q r : Pos} (h1 : PLE p q) (h2 : PLE q r) : PLE p r := by
  unfold PLE at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left; omega
  · left; omega
  · left; omega
  · right; exact ⟨h1.trans h2, h1'.trans h2'⟩

theorem posLE_iff (p q : Pos) : posLE p q = true ↔ PLE p q := by
  unfold posLE PLE; simp

/-- Prefix of a valid position `p ≤ q` taken inside the prefix at `q`. -/
theorem valid_in_prefix (R : Piece) (p q : Pos) (hp : R.ValidPos p) (hq : R.ValidPos q)
    (hpq : PLE p q) : (prefixList R q).ValidPos p ∧ prefixList (prefixList R q) p = prefixList R p := by
  obtain ⟨hpk, hpa, hpb⟩ := hp
  obtain ⟨hqk, hqa, hqb⟩ := hq
  have hp1 : p.1 ≤ q.1 := by rcases hpq with h | ⟨h, -⟩ <;> omega
  have hlen : (prefixList R q).length = q.1 + 1 := by
    simp [prefixList, hqk]; omega
  have hget : (prefixList R q).getD p.1 default =
      if p.1 < q.1 then R.getD p.1 default else ⟨(R.getD q.1 default).a, q.2⟩ := by
    simp only [prefixList, if_pos hqk]
    split_ifs with h
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega : p.1 < (List.take q.1 R).length), h]
    · have he : p.1 = q.1 := by omega
      rw [he, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by simp only [List.length_take]; omega)]
      simp [Nat.min_eq_left hqk.le]
  have hv : (prefixList R q).ValidPos p := by
    refine ⟨by omega, ?_, ?_⟩
    · rw [hget]; split_ifs with h
      · exact hpa
      · have he : p.1 = q.1 := by omega
        rw [← he]; exact hpa
    · rw [hget]; split_ifs with h
      · exact hpb
      · rcases hpq with h' | ⟨-, h'⟩
        · omega
        · exact h'
  refine ⟨hv, ?_⟩
  simp only [prefixList, if_pos hqk, if_pos hpk]
  rw [if_pos (by simp; omega)]
  have hget' := hget
  simp only [prefixList, if_pos hqk] at hget'
  rw [hget']
  congr 1
  · rw [List.take_append_of_le_length (by simp; omega), List.take_take, min_eq_left hp1]
  · split_ifs with h
    · rfl
    · have he : p.1 = q.1 := by omega
      rw [he]
section cells
variable (R : Piece) (hR : R.WF)
include hR

theorem cdp (P : Piece) (hP : P.WF) (p : Pos) (hp : P.ValidPos p) :
    (prefixList P p).WF ∧ (suffixList P p).WF ∧
    Disjoint (prefixList P p).toSet (suffixList P p).toSet ∧
    (prefixList P p).toSet ∪ (suffixList P p).toSet = P.toSet :=
  cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1 P hP p hp

omit hR in
theorem cdp' (P : Piece) (hP : P.WF) (p : Pos) (hp : P.ValidPos p) :
    (suffixList P p).toSet = P.toSet \ (prefixList P p).toSet := by
  obtain ⟨-, -, hd, hu⟩ := cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1 P hP p hp
  rw [← hu]; ext x; simp only [Set.mem_union, Set.mem_sdiff]
  constructor
  · intro h; exact ⟨Or.inr h, fun h' => Set.disjoint_left.mp hd h' h⟩
  · rintro ⟨h | h, hn⟩
    · exact absurd h hn
    · exact h

theorem pre_mono (p q : Pos) (hp : R.ValidPos p) (hq : R.ValidPos q) (hpq : PLE p q) :
    (prefixList R p).toSet ⊆ (prefixList R q).toSet := by
  obtain ⟨hv, he⟩ := valid_in_prefix R p q hp hq hpq
  have hqwf := (cdp R hR R hR q hq).1
  rw [← he, ← (cdp R hR _ hqwf p hv).2.2.2]
  exact Set.subset_union_left

theorem pre_sub (q : Pos) (hq : R.ValidPos q) : (prefixList R q).toSet ⊆ R.toSet := by
  rw [← (cdp R hR R hR q hq).2.2.2]; exact Set.subset_union_left

theorem cell_set (p q : Pos) (hp : R.ValidPos p) (hq : R.ValidPos q) (hpq : PLE p q) :
    (suffixList (prefixList R q) p).WF ∧
    (suffixList (prefixList R q) p).toSet = (prefixList R q).toSet \ (prefixList R p).toSet := by
  obtain ⟨hv, he⟩ := valid_in_prefix R p q hp hq hpq
  have hqwf := (cdp R hR R hR q hq).1
  refine ⟨(cdp R hR _ hqwf p hv).2.1, ?_⟩
  rw [cdp' _ hqwf p hv, he]

/-- The start position `(0, a₀)` of a nonempty piece. -/
theorem start_pos (hne : R ≠ []) :
    R.ValidPos (0, (R.getD 0 default).a) ∧ (prefixList R (0, (R.getD 0 default).a)).toSet = ∅ ∧
    ∀ p : Pos, R.ValidPos p → PLE (0, (R.getD 0 default).a) p := by
  have h0 : 0 < R.length := List.length_pos_of_ne_nil hne
  have hI := hR.1 (R.getD 0 default) (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0]; exact List.getElem_mem _)
  refine ⟨⟨h0, le_rfl, hI.2.1⟩, ?_, ?_⟩
  · ext x; simp [prefixList, h0, Piece.toSet, Interval.toSet]
  · rintro p ⟨hpk, hpa, -⟩
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · right; exact ⟨h.symm, by rw [h] at hpa; exact hpa⟩
    · left; exact h

end cells

/-- Monotone step function with a grid of attained values has small steps. -/
theorem small_steps (f : ℕ → ℝ) (m M : ℕ) (v : ℝ) (hM : 1 ≤ M)
    (hmono : ∀ j j', j ≤ j' → j' ≤ m + 1 → f j ≤ f j') (h0 : f 0 = 0) (hv : f (m + 1) = v)
    (hgrid : ∀ t, 1 ≤ t → t ≤ M - 1 → ∃ j ≤ m + 1, f j = t * v / M) :
    ∀ k ≤ m, f (k + 1) - f k ≤ v / M := by
  intro k hk
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hv0 : 0 ≤ v := by rw [← hv, ← h0]; exact hmono 0 (m + 1) (by omega) le_rfl
  rcases eq_or_lt_of_le hv0 with hv0 | hvpos
  · have := hmono k (k + 1) (by omega) (by omega)
    have := hmono (k + 1) (m + 1) (by omega) le_rfl
    have := hmono 0 k (by omega) (by omega)
    rw [← hv0]; rw [← hv0] at hv; simp only [zero_div]; linarith
  by_contra hcon
  push Not at hcon
  have hfk0 : 0 ≤ f k := by rw [← h0]; exact hmono 0 k (by omega) (by omega)
  set t := ⌊f k * M / v⌋₊ + 1 with ht
  have hfl := Nat.lt_floor_add_one (f k * M / v)
  have hfl' := Nat.floor_le (div_nonneg (mul_nonneg hfk0 hMpos.le) hvpos.le)
  have htv1 : f k < t * v / M := by
    rw [lt_div_iff₀ hMpos]
    rw [div_lt_iff₀ hvpos] at hfl
    push_cast [ht]; nlinarith
  have htv2 : (t : ℝ) * v / M ≤ f k + v / M := by
    rw [div_le_iff₀ hMpos]
    rw [le_div_iff₀ hvpos] at hfl'
    push_cast [ht]
    have : (f k + v / M) * M = f k * M + v := by field_simp
    rw [this]; nlinarith
  have hfk1 : f (k + 1) ≤ v := by rw [← hv]; exact hmono (k + 1) (m + 1) (by omega) le_rfl
  have ht1 : 1 ≤ t := by omega
  have htM : t ≤ M - 1 := by
    by_contra h
    have : (M : ℝ) ≤ t := by exact_mod_cast (show M ≤ t by omega)
    have : v ≤ t * v / M := by rw [le_div_iff₀ hMpos]; nlinarith
    linarith
  obtain ⟨j, hj, hfj⟩ := hgrid t ht1 htM
  rcases Nat.lt_or_ge k j with h | h
  · have := hmono (k + 1) j (by omega) hj
    linarith
  · have := hmono j k h (by omega)
    linarith
/-- Boundary sets: the prefix up to the `k`-th listed position, and the whole piece afterwards. -/
noncomputable def bnd (R : Piece) (pts : List Pos) (k : ℕ) : Set ℝ :=
  if h : k < pts.length then (prefixList R pts[k]).toSet else R.toSet

theorem bnd_mono (R : Piece) (hR : R.WF) (pts : List Pos) (hv : ∀ p ∈ pts, R.ValidPos p)
    (hs : pts.Pairwise PLE) : ∀ k k', k ≤ k' → bnd R pts k ⊆ bnd R pts k' := by
  intro k k' hkk'
  unfold bnd
  split_ifs with h1 h2 h2
  · rcases eq_or_lt_of_le hkk' with rfl | hlt
    · exact subset_rfl
    · exact pre_mono R hR _ _ (hv _ (List.getElem_mem _)) (hv _ (List.getElem_mem _))
        (List.pairwise_iff_getElem.mp hs k k' h1 h2 hlt)
  · exact pre_sub R hR _ (hv _ (List.getElem_mem _))
  · omega
  · exact subset_rfl

theorem aligned_suffix {ι : Type} (t : Rec ι) (P : Piece) (p : Pos) (hp : P.ValidPos p)
    (hP : t.Aligned P) (hp2 : p.2 ∈ t.pts) : t.Aligned (suffixList P p) := by
  obtain ⟨hk, -, -⟩ := hp
  intro I hI
  simp only [suffixList, if_pos hk, List.mem_cons] at hI
  rcases hI with rfl | hI
  · refine ⟨hp2, ?_⟩
    have hmem : P.getD p.1 default ∈ P := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem _
    exact (hP _ hmem).2
  · exact hP I (List.mem_of_mem_drop hI)

theorem pt_of_prefix {ι : Type} (t : Rec ι) (R : Piece) (p : Pos) (hp : R.ValidPos p)
    (h : t.Aligned (prefixList R p)) : p.2 ∈ t.pts := by
  have hk := hp.1
  have : (⟨(R.getD p.1 default).a, p.2⟩ : Interval) ∈ prefixList R p := by
    simp [prefixList, hk]
  exact (h _ this).2

theorem cellsAux_spec {ι : Type} (R : Piece) (hR : R.WF) (t : Rec ι) (hRt : t.Aligned R) :
    ∀ (l : List Pos) (prev : Pos), R.ValidPos prev → (∀ p ∈ l, R.ValidPos p) →
    List.Pairwise PLE (prev :: l) →
    (∀ p ∈ prev :: l, t.Aligned (prefixList R p)) →
    (cellsAux R prev l).length = l.length + 1 ∧
    ∀ k ≤ l.length, ((cellsAux R prev l).getD k []).WF ∧
      t.Aligned ((cellsAux R prev l).getD k []) ∧
      ((cellsAux R prev l).getD k []).toSet = bnd R (prev :: l) (k + 1) \ bnd R (prev :: l) k := by
  intro l
  induction l with
  | nil =>
    intro prev hprev _ _ hal
    refine ⟨rfl, fun k hk => ?_⟩
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp only [cellsAux, List.getD_cons_zero]
    refine ⟨(cdp R hR R hR prev hprev).2.1,
      aligned_suffix t R prev hprev hRt (pt_of_prefix t R prev hprev (hal prev (List.mem_cons_self ..))), ?_⟩
    rw [cdp' R hR prev hprev]
    simp [bnd]
  | cons p ps ih =>
    intro prev hprev hv hs hal
    have hp : R.ValidPos p := hv p (List.mem_cons_self ..)
    have hpp : PLE prev p := (List.pairwise_cons.mp hs).1 p (List.mem_cons_self ..)
    obtain ⟨ihl, ihk⟩ := ih p hp (fun q hq => hv q (List.mem_cons_of_mem _ hq))
      (List.pairwise_cons.mp hs).2 (fun q hq => hal q (List.mem_cons_of_mem _ hq))
    refine ⟨by simp [cellsAux, ihl], fun k hk => ?_⟩
    cases k with
    | zero =>
      simp only [cellsAux, List.getD_cons_zero]
      obtain ⟨hwf, hset⟩ := cell_set R hR prev p hprev hp hpp
      obtain ⟨hvin, -⟩ := valid_in_prefix R prev p hprev hp hpp
      refine ⟨hwf, aligned_suffix t _ prev hvin (hal p (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        (pt_of_prefix t R prev hprev (hal prev (List.mem_cons_self ..))), ?_⟩
      rw [hset]
      simp [bnd]
    | succ k =>
      simp only [cellsAux, List.getD_cons_succ]
      obtain ⟨h1, h2, h3⟩ := ihk k (by simp at hk; omega)
      refine ⟨h1, h2, ?_⟩
      rw [h3]
      simp [bnd]

/-- The cells of Repair: well formed, aligned, pairwise disjoint, covering `R`, and given by
consecutive boundary sets of the sorted marks. -/
theorem cellsOf_spec {ι : Type} (R : Piece) (hR : R.WF) (hne : R ≠ []) (t : Rec ι)
    (hRt : t.Aligned R) (marks : List Pos) (hv : ∀ p ∈ marks, R.ValidPos p)
    (hal : ∀ p ∈ marks, t.Aligned (prefixList R p)) :
    let pts := (0, (R.getD 0 default).a) :: marks.mergeSort posLE
    (cellsOf R marks).length = marks.length + 1 ∧
    (∀ k ≤ marks.length, ((cellsOf R marks).getD k []).WF ∧
      t.Aligned ((cellsOf R marks).getD k []) ∧
      ((cellsOf R marks).getD k []).toSet = bnd R pts (k + 1) \ bnd R pts k) ∧
    (∀ k k', k ≤ k' → bnd R pts k ⊆ bnd R pts k') ∧
    bnd R pts 0 = ∅ ∧ bnd R pts (marks.length + 1) = R.toSet ∧
    (∀ p ∈ marks, ∃ j ≤ marks.length + 1, bnd R pts j = (prefixList R p).toSet) := by
  intro pts
  obtain ⟨hp0, hpre0, hle0⟩ := start_pos R hR hne
  have hsorted : (marks.mergeSort posLE).Pairwise PLE := by
    have := List.pairwise_mergeSort (le := posLE)
      (fun a b c hab hbc => (posLE_iff a c).mpr (PLE_trans ((posLE_iff a b).mp hab) ((posLE_iff b c).mp hbc)))
      (fun a b => by
        unfold posLE
        rcases lt_trichotomy a.1 b.1 with h | h | h
        · simp [h]
        · rcases le_total a.2 b.2 with h' | h' <;> simp [h, h']
        · simp [h, Nat.lt_asymm h]) marks
    exact this.imp (fun h => (posLE_iff _ _).mp h)
  have hvs : ∀ p ∈ marks.mergeSort posLE, R.ValidPos p := fun p hp => hv p (List.mem_mergeSort.mp hp)
  have hvpts : ∀ p ∈ pts, R.ValidPos p := by
    intro p hp; rcases List.mem_cons.mp hp with rfl | hp
    · exact hp0
    · exact hvs p hp
  have hspts : pts.Pairwise PLE :=
    List.pairwise_cons.mpr ⟨fun p hp => hle0 p (hvs p hp), hsorted⟩
  have halpts : ∀ p ∈ pts, t.Aligned (prefixList R p) := by
    intro p hp; rcases List.mem_cons.mp hp with rfl | hp
    · intro I hI
      have hk := hp0.1
      simp only [prefixList, if_pos hk, List.take_zero, List.nil_append, List.mem_singleton] at hI
      subst hI
      have hmem : R.getD 0 default ∈ R := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem _
      exact ⟨(hRt _ hmem).1, (hRt _ hmem).1⟩
    · exact hal p (List.mem_mergeSort.mp hp)
  obtain ⟨hlen, hk⟩ := cellsAux_spec R hR t hRt _ _ hp0 hvs hspts halpts
  have hlm : (marks.mergeSort posLE).length = marks.length := List.length_mergeSort _
  refine ⟨by unfold cellsOf; rw [hlen, hlm], fun k hk' => ?_, bnd_mono R hR pts hvpts hspts, ?_, ?_, ?_⟩
  · unfold cellsOf; exact hk k (by rw [hlm]; exact hk')
  · unfold bnd; rw [dif_pos (by simp [pts])]; simpa [pts] using hpre0
  · simp [bnd, pts, hlm]
  · intro p hp
    obtain ⟨j, hj, hjp⟩ := List.getElem_of_mem ((List.mem_mergeSort (le := posLE)).mpr hp)
    refine ⟨j + 1, by rw [hlm] at hj; omega, ?_⟩
    simp only [bnd, pts, List.length_cons]
    rw [dif_pos (by omega)]
    simp [hjp]
theorem cellsAux_nil_piece : ∀ (l : List Pos) (prev : Pos), ∀ c ∈ cellsAux [] prev l, c = [] := by
  intro l
  induction l with
  | nil => intro prev c hc; simp [cellsAux, suffixList] at hc; exact hc
  | cons p ps ih =>
    intro prev c hc
    simp only [cellsAux, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp [suffixList, prefixList]
    · exact ih p c hc

/-- Telescoping union of consecutive differences of a monotone family. -/
theorem union_steps (b : ℕ → Set ℝ) (hb : ∀ k k', k ≤ k' → b k ⊆ b k') :
    ∀ m, (⋃ k ∈ Finset.range m, (b (k + 1) \ b k)) = b m \ b 0 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert, ih]
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, fun h => h2 (hb 0 m (by omega) h)⟩
      · exact ⟨hb m (m + 1) (by omega) h1, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases h : x ∈ b m
      · exact Or.inr ⟨h, h2⟩
      · exact Or.inl ⟨h1, h⟩

/-- Facts about the cells of Repair used throughout. -/
theorem cells_facts {ι : Type} (R : Piece) (hR : R.WF) (t : Rec ι) (hRt : t.Aligned R)
    (marks : List Pos) (hv : R ≠ [] → ∀ p ∈ marks, R.ValidPos p ∧ t.Aligned (prefixList R p)) :
    let cells := cellsOf R marks
    (∀ k, (cells.getD k []).WF ∧ t.Aligned (cells.getD k [])) ∧
    (∀ k k', k ≠ k' → Disjoint (cells.getD k []).toSet (cells.getD k' []).toSet) ∧
    (⋃ k ∈ Finset.range cells.length, (cells.getD k []).toSet) = R.toSet := by
  intro cells
  by_cases hne : R = []
  · subst hne
    have hall : ∀ k, cells.getD k [] = [] := by
      intro k
      rw [List.getD_eq_getElem?_getD]
      rcases h : cells[k]? with _ | c
      · rfl
      · exact cellsAux_nil_piece _ _ c (List.mem_of_getElem? h)
    refine ⟨fun k => by rw [hall k]; exact ⟨wf_nil, fun I hI => by simp at hI⟩,
      fun k k' _ => by rw [hall k, toSet_nil]; exact Set.empty_disjoint _, ?_⟩
    have : ∀ k, (cells.getD k []).toSet = ∅ := fun k => by rw [hall k, toSet_nil]
    simp only [this, Set.iUnion_empty, toSet_nil]
  obtain ⟨hlen, hk, hmono, h0, hend, -⟩ := cellsOf_spec R hR hne t hRt marks
    (fun p hp => (hv hne p hp).1) (fun p hp => (hv hne p hp).2)
  set pts := (0, (R.getD 0 default).a) :: marks.mergeSort posLE
  have hout : ∀ k, marks.length < k → cells.getD k [] = [] := by
    intro k hk'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by show (cellsOf R marks).length ≤ k; omega)]
    rfl
  have hcell : ∀ k ≤ marks.length, (cells.getD k []).toSet = bnd R pts (k + 1) \ bnd R pts k :=
    fun k hk' => (hk k hk').2.2
  refine ⟨fun k => ?_, fun k k' hkk' => ?_, ?_⟩
  · by_cases hkm : k ≤ marks.length
    · exact ⟨(hk k hkm).1, (hk k hkm).2.1⟩
    · rw [hout k (by omega)]; exact ⟨wf_nil, fun I hI => by simp at hI⟩
  · by_cases hkm : k ≤ marks.length
    · by_cases hkm' : k' ≤ marks.length
      · rw [hcell k hkm, hcell k' hkm']
        rcases Nat.lt_or_gt_of_ne hkk' with h | h
        · exact Disjoint.mono_left (Set.sdiff_subset.trans (hmono (k + 1) k' (by omega)))
            Set.disjoint_sdiff_right
        · exact Disjoint.mono_right (Set.sdiff_subset.trans (hmono (k' + 1) k (by omega)))
            Set.disjoint_sdiff_left
      · rw [hout k' (by omega), toSet_nil]; exact Set.disjoint_empty _
    · rw [hout k (by omega), toSet_nil]; exact Set.empty_disjoint _
  · rw [hlen]
    have : (⋃ k ∈ Finset.range (marks.length + 1), (cells.getD k []).toSet) =
        ⋃ k ∈ Finset.range (marks.length + 1), (bnd R pts (k + 1) \ bnd R pts k) := by
      apply Set.iUnion₂_congr; intro k hk'
      exact hcell k (by simp at hk'; omega)
    rw [this, union_steps _ hmono, hend, h0, Set.diff_empty]

theorem toSet_flatten_map (f : ℕ → Piece) (l : List ℕ) :
    Piece.toSet (l.map f).flatten = ⋃ c ∈ l, (f c).toSet := by
  induction l with
  | nil => simp [toSet_nil]
  | cons a l ih =>
    simp only [List.map_cons, List.flatten_cons, toSet_append, ih, List.mem_cons]
    ext x; simp only [Set.mem_union, Set.mem_iUnion, exists_prop]
    constructor
    · rintro (h | ⟨c, hc, h⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨c, Or.inr hc, h⟩
    · rintro ⟨c, rfl | hc, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨c, hc, h⟩

theorem flat_wf (f : ℕ → Piece) (hf : ∀ c, (f c).WF)
    (hd : ∀ c c', c ≠ c' → Disjoint (f c).toSet (f c').toSet) :
    ∀ l : List ℕ, l.Nodup → Piece.WF (l.map f).flatten := by
  intro l
  induction l with
  | nil => intro _; exact wf_nil
  | cons a l ih =>
    intro hnd
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.flatten_cons]
    refine wf_append _ _ (hf a) (ih hnd.2) ?_
    rw [toSet_flatten_map]
    rw [Set.disjoint_iUnion₂_right]
    intro c hc
    exact hd a c (fun h => hnd.1 (h ▸ hc))

theorem flat_aligned {ι : Type} (t : Rec ι) (f : ℕ → Piece) (hf : ∀ c, t.Aligned (f c)) :
    ∀ l : List ℕ, t.Aligned (l.map f).flatten := by
  intro l
  induction l with
  | nil => intro I hI; simp at hI
  | cons a l ih =>
    simp only [List.map_cons, List.flatten_cons]
    exact aligned_append t _ _ (hf a) ih
theorem flatten_update_perm {ι : Type} [DecidableEq ι] (Q : ι → List ℕ) (i : ι) (c : ℕ) :
    ∀ (order : List ι), order.Nodup → i ∈ order →
    ((order.map (Function.update Q i (Q i ++ [c]))).flatten).Perm
      ((order.map Q).flatten ++ [c]) := by
  intro order
  induction order with
  | nil => intro _ h; simp at h
  | cons a as ih =>
    intro hnd hi
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.flatten_cons]
    by_cases hai : a = i
    · subst hai
      have hmap : as.map (Function.update Q a (Q a ++ [c])) = as.map Q := by
        apply List.map_congr_left; intro x hx
        rw [Function.update_of_ne (by rintro rfl; exact hnd.1 hx)]
      rw [hmap, Function.update_self, List.append_assoc]
      exact (List.perm_append_comm.append_left (Q a)).trans (by simp)
    · rw [Function.update_of_ne hai, List.append_assoc]
      have hi' : i ∈ as := by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h.symm hai
        · exact h
      exact (ih hnd.2 hi').append_left _

/-- The round-robin bookkeeping invariant: picks and available cells partition the indices. -/
theorem rr_perm {ι : Type} [DecidableEq ι] (V : ι → Valuation) (cells : List Piece)
    (order : List ι) (hnd : order.Nodup) (L : ℕ) :
    ∀ (rem : List ι) (avail : List ℕ) (Q : ι → List ℕ) (t : Rec ι) (o : ChoiceOracle ι)
      (tr₀ : List (Event ι)) (Q' : ι → List ℕ) (avail' : List ℕ) (t' : Rec ι)
      (tr : List (Event ι)), (∀ i ∈ rem, i ∈ order) →
      ((order.map Q).flatten ++ avail).Perm (List.range L) →
      Prog.run V o ((rrRound cells rem avail Q).run t) tr₀ = some (((Q', avail'), t'), tr) →
      t' = t ∧ ((order.map Q').flatten ++ avail').Perm (List.range L) ∧
      (∀ i, i ∉ order → Q' i = Q i) := by
  intro rem
  induction rem with
  | nil =>
    intro avail Q t o tr₀ Q' avail' t' tr _ hp h
    simp only [rrRound] at h
    rw [run_pure'] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, -⟩ := h
    exact ⟨rfl, hp, fun _ _ => rfl⟩
  | cons i is ih =>
    intro avail Q t o tr₀ Q' avail' t' tr hrem hp h
    simp only [rrRound] at h
    rw [run_stbind] at h
    rcases hpk : Prog.run V o ((rrPick cells avail i).run t) tr₀ with _ | ⟨⟨c, t1⟩, tr1⟩
    · rw [hpk] at h; simp at h
    · rw [hpk] at h
      dsimp only at h
      unfold rrPick at hpk
      rw [run_stbind, run_get'] at hpk
      dsimp only at hpk
      obtain ⟨ht1, hc⟩ := choose_state V o _ t _ c t1 tr1 hpk
      rw [ht1] at h
      have hcav : c ∈ avail := (List.mem_filter.mp hc).1
      have hio : i ∈ order := hrem i (List.mem_cons_self ..)
      have hp' : ((order.map (Function.update Q i (Q i ++ [c]))).flatten ++ avail.erase c).Perm
          (List.range L) := by
        refine (List.Perm.append_right _ (flatten_update_perm Q i c order hnd hio)).trans ?_
        rw [List.append_assoc]
        exact (List.Perm.append_left _ (List.perm_cons_erase hcav).symm).trans hp
      obtain ⟨h1, h2, h3⟩ := ih (avail.erase c) _ t o tr1 Q' avail' t' tr
        (fun j hj => hrem j (List.mem_cons_of_mem _ hj)) hp' h
      refine ⟨h1, h2, fun j hj => ?_⟩
      rw [h3 j hj, Function.update_of_ne (by rintro rfl; exact hj hio)]

theorem rr_perm_rounds {ι : Type} [DecidableEq ι] (V : ι → Valuation) (cells : List Piece)
    (order : List ι) (hnd : order.Nodup) (L : ℕ) :
    ∀ (r : ℕ) (avail : List ℕ) (Q : ι → List ℕ) (t : Rec ι) (o : ChoiceOracle ι)
      (tr₀ : List (Event ι)) (Q' : ι → List ℕ) (avail' : List ℕ) (t' : Rec ι)
      (tr : List (Event ι)),
      ((order.map Q).flatten ++ avail).Perm (List.range L) →
      Prog.run V o ((roundRobin cells order r avail Q).run t) tr₀ = some (((Q', avail'), t'), tr) →
      t' = t ∧ ((order.map Q').flatten ++ avail').Perm (List.range L) ∧
      (∀ i, i ∉ order → Q' i = Q i) := by
  intro r
  induction r with
  | zero =>
    intro avail Q t o tr₀ Q' avail' t' tr hp h
    simp only [roundRobin] at h
    rw [run_pure'] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, -⟩ := h
    exact ⟨rfl, hp, fun _ _ => rfl⟩
  | succ r ih =>
    intro avail Q t o tr₀ Q' avail' t' tr hp h
    simp only [roundRobin] at h
    rw [run_stbind] at h
    rcases hrd : Prog.run V o ((rrRound cells order avail Q).run t) tr₀ with
      _ | ⟨⟨⟨Q1, a1⟩, t1⟩, tr1⟩
    · rw [hrd] at h; simp at h
    · rw [hrd] at h
      dsimp only at h
      obtain ⟨ht1, hp1, hq1⟩ := rr_perm V cells order hnd L order avail Q t o tr₀ Q1 a1 t1 tr1
        (fun i hi => hi) hp hrd
      rw [ht1] at h
      obtain ⟨h1, h2, h3⟩ := ih a1 Q1 t o tr1 Q' avail' t' tr hp1 h
      exact ⟨h1, h2, fun i hi => (h3 i hi).trans (hq1 i hi)⟩
section rrfwd
variable {ι : Type} [DecidableEq ι] (V : ι → Valuation) (cells : List Piece) (order : List ι)
  (hnd : order.Nodup) (st : Rec ι) (L : ℕ)

/-- The round-robin invariant. -/
def RRI (Q : ι → List ℕ) (avail : List ℕ) : Prop :=
  ((order.map Q).flatten ++ avail).Perm (List.range L) ∧
  (∀ i ∈ order, ∀ c ∈ Q i, ∀ c' ∈ avail,
    st.pieceVal i (cells.getD c' []) ≤ st.pieceVal i (cells.getD c [])) ∧
  (∀ i ∈ order, ∀ j ∈ order, ∀ r r', r < r' → ∀ (hr' : r' < (Q j).length) (hr : r < (Q i).length),
    st.pieceVal i (cells.getD (Q j)[r'] []) ≤ st.pieceVal i (cells.getD (Q i)[r] []))

include hnd in
theorem rrRound_fwd : ∀ (rem : List ι) (k : ℕ) (avail : List ℕ) (Q : ι → List ℕ)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
    rem.Nodup → (∀ i ∈ rem, i ∈ order) → RRI cells order st L Q avail →
    (∀ i ∈ order, (Q i).length = if i ∈ rem then k else k + 1) → rem.length ≤ avail.length →
    ∃ (Q' : ι → List ℕ) (avail' : List ℕ) (tr : List (Event ι)),
      Prog.run V o ((rrRound cells rem avail Q).run st) tr₀ = some (((Q', avail'), st), tr) ∧
      queryCount tr = queryCount tr₀ ∧ RRI cells order st L Q' avail' ∧
      (∀ i ∈ order, (Q' i).length = k + 1) ∧ avail'.length + rem.length = avail.length := by
  intro rem
  induction rem with
  | nil =>
    intro k avail Q o tr₀ _ _ hI hlen _
    refine ⟨Q, avail, tr₀, rfl, rfl, hI, fun i hi => by simpa using hlen i hi, by simp⟩
  | cons i is ih =>
    intro k avail Q o tr₀ hrnd hrem hI hlen hav
    rw [List.nodup_cons] at hrnd
    have hio : i ∈ order := hrem i (List.mem_cons_self ..)
    obtain ⟨hperm, hdom, hpair⟩ := hI
    let val : ℕ → ℝ := fun c => st.pieceVal i (cells.getD c [])
    have havne : avail ≠ [] := by intro h; rw [h] at hav; simp at hav
    obtain ⟨c0, hc0, hmax⟩ := Finset.exists_max_image avail.toFinset val
      (by rw [List.toFinset_nonempty_iff]; exact havne)
    let F := avail.filter (fun c => decide (∀ d ∈ avail,
      st.pieceVal i (cells.getD d []) ≤ st.pieceVal i (cells.getD c [])))
    have hFne : F ≠ [] := by
      apply List.ne_nil_of_mem (a := c0)
      simp only [F, List.mem_filter, decide_eq_true_eq]
      exact ⟨List.mem_toFinset.mp hc0, fun d hd => hmax d (List.mem_toFinset.mpr hd)⟩
    obtain ⟨c, hcF, tr1, hrun1, hq1⟩ := run_choose_ex V o F hFne st tr₀
    simp only [F, List.mem_filter, decide_eq_true_eq] at hcF
    obtain ⟨hcav, hcmax⟩ := hcF
    let Q1 := Function.update Q i (Q i ++ [c])
    have hQ1i : Q1 i = Q i ++ [c] := Function.update_self ..
    have hQ1j : ∀ j, j ≠ i → Q1 j = Q j := fun j hj => Function.update_of_ne hj ..
    have hleni : (Q i).length = k := by simpa [hrem] using hlen i hio
    have hlenge : ∀ j ∈ order, k ≤ (Q j).length := by
      intro j hj; rw [hlen j hj]; split_ifs <;> omega
    have hI1 : RRI cells order st L Q1 (avail.erase c) := by
      refine ⟨?_, ?_, ?_⟩
      · refine (List.Perm.append_right _ (flatten_update_perm Q i c order hnd hio)).trans ?_
        rw [List.append_assoc]
        exact (List.Perm.append_left _ (List.perm_cons_erase hcav).symm).trans hperm
      · intro j hj c' hc' c'' hc''
        have hc''a : c'' ∈ avail := List.mem_of_mem_erase hc''
        by_cases hji : j = i
        · subst hji
          rw [hQ1i, List.mem_append] at hc'
          rcases hc' with hc' | hc'
          · exact hdom j hj c' hc' c'' hc''a
          · simp at hc'; subst hc'; exact hcmax c'' hc''a
        · rw [hQ1j j hji] at hc'; exact hdom j hj c' hc' c'' hc''a
      · intro i' hi' j hj r r' hrr' hr' hr
        -- the new element of `Q1 i` is the cell `c`
        have hnew : ∀ (hr' : r' < (Q1 j).length), j = i → r' = k →
            st.pieceVal i' (cells.getD (Q1 j)[r'] []) ≤ st.pieceVal i' (cells.getD (Q1 i')[r] []) := by
          intro hr'' hji hrk
          subst hji
          have hrq : r < (Q i').length := by have := hlenge i' hi'; omega
          have e1 : (Q1 j)[r'] = c := by
            simp only [hQ1i, hrk]; rw [List.getElem_append_right (by omega)]; simp [hleni]
          have e2 : (Q1 i')[r] = (Q i')[r] := by
            by_cases hii : i' = j
            · subst hii; simp only [hQ1i]; rw [List.getElem_append_left hrq]
            · simp only [hQ1j i' hii]
          rw [e1, e2]
          exact hdom i' hi' _ (List.getElem_mem hrq) c hcav
        by_cases hji : j = i
        · by_cases hrk : r' = k
          · exact hnew hr' hji hrk
          · subst hji
            have hr'q : r' < (Q j).length := by
              rw [hQ1i] at hr'; simp at hr'; omega
            have e1 : (Q1 j)[r'] = (Q j)[r'] := by
              simp only [hQ1i]; rw [List.getElem_append_left hr'q]
            have hrq : r < (Q i').length := by
              by_cases hii : i' = j
              · subst hii; omega
              · rw [hQ1j i' hii] at hr; exact hr
            have e2 : (Q1 i')[r] = (Q i')[r] := by
              by_cases hii : i' = j
              · subst hii; simp only [hQ1i]; rw [List.getElem_append_left hrq]
              · simp only [hQ1j i' hii]
            rw [e1, e2]; exact hpair i' hi' j hj r r' hrr' hr'q hrq
        · have hr'q : r' < (Q j).length := by rw [hQ1j j hji] at hr'; exact hr'
          have e1 : (Q1 j)[r'] = (Q j)[r'] := by simp only [hQ1j j hji]
          have hrq : r < (Q i').length := by
            by_cases hii : i' = i
            · subst hii
              have := hlen j hj
              have hlj : (Q j).length ≤ k + 1 := by rw [this]; split_ifs <;> omega
              omega
            · rw [hQ1j i' hii] at hr; exact hr
          have e2 : (Q1 i')[r] = (Q i')[r] := by
            by_cases hii : i' = i
            · subst hii; simp only [hQ1i]; rw [List.getElem_append_left hrq]
            · simp only [hQ1j i' hii]
          rw [e1, e2]; exact hpair i' hi' j hj r r' hrr' hr'q hrq
    have hlen1 : ∀ j ∈ order, (Q1 j).length = if j ∈ is then k else k + 1 := by
      intro j hj
      by_cases hji : j = i
      · subst hji; rw [hQ1i, if_neg hrnd.1]; simp [hleni]
      · rw [hQ1j j hji, hlen j hj]
        simp [hji]
    have hav1 : (avail.erase c).length = avail.length - 1 := List.length_erase_of_mem hcav
    obtain ⟨Q', avail', tr, hr, hq, hI', hlen', hav'⟩ := ih k (avail.erase c) Q1 o tr1 hrnd.2
      (fun j hj => hrem j (List.mem_cons_of_mem _ hj)) hI1 hlen1 (by simp at hav; omega)
    refine ⟨Q', avail', tr, ?_, hq.trans hq1, hI', hlen', by simp at hav ⊢; omega⟩
    simp only [rrRound]
    rw [run_stbind]
    unfold rrPick
    rw [run_stbind, run_get']
    dsimp only
    rw [hrun1]
    dsimp only
    exact hr

include hnd in
theorem roundRobin_fwd : ∀ (r k : ℕ) (avail : List ℕ) (Q : ι → List ℕ) (o : ChoiceOracle ι)
    (tr₀ : List (Event ι)), RRI cells order st L Q avail →
    (∀ i ∈ order, (Q i).length = k) → r * order.length ≤ avail.length →
    ∃ (Q' : ι → List ℕ) (avail' : List ℕ) (tr : List (Event ι)),
      Prog.run V o ((roundRobin cells order r avail Q).run st) tr₀ = some (((Q', avail'), st), tr) ∧
      queryCount tr = queryCount tr₀ ∧ RRI cells order st L Q' avail' ∧
      (∀ i ∈ order, (Q' i).length = k + r) := by
  intro r
  induction r with
  | zero =>
    intro k avail Q o tr₀ hI hlen _
    exact ⟨Q, avail, tr₀, rfl, rfl, hI, fun i hi => by simpa using hlen i hi⟩
  | succ r ih =>
    intro k avail Q o tr₀ hI hlen hav
    obtain ⟨Q1, a1, tr1, hr1, hq1, hI1, hlen1, hav1⟩ := rrRound_fwd V cells order hnd st L order k
      avail Q o tr₀ hnd (fun i hi => hi) hI (fun i hi => by simp [hi, hlen i hi])
      (by nlinarith)
    obtain ⟨Q', a', tr, hr, hq, hI', hlen'⟩ := ih (k + 1) a1 Q1 o tr1 hI1 hlen1
      (by rw [Nat.succ_mul] at hav; omega)
    refine ⟨Q', a', tr, ?_, hq.trans hq1, hI', fun i hi => by rw [hlen' i hi]; ring⟩
    simp only [roundRobin]
    rw [run_stbind, hr1]
    dsimp only
    exact hr

end rrfwd
theorem marksOf_ok {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) (R : Piece)
    (hR : R.WF) (hne : R ≠ []) (i : ι) (hi : i ∈ N) (v : ℝ) (M : ℕ) :
    ∀ (ts : List ℕ), (∀ t ∈ ts, 0 ≤ (t : ℝ) * v / M ∧ (t : ℝ) * v / M ≤ (V i).value R.toSet) →
    ∀ (s : Rec ι), s.Valid V N → s.Aligned R → ∀ (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
    ∃ (ps : List Pos) (s' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((marksOf N R i v M ts).run s) tr₀ = some ((ps, s'), tr) ∧
      s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ ps.length = ts.length ∧
      (∀ p ∈ ps, R.ValidPos p ∧ s'.Aligned (prefixList R p)) ∧
      (∀ k (hk : k < ps.length), (V i).value (prefixList R ps[k]).toSet =
        (ts.getD k 0 : ℝ) * v / M) ∧
      s'.prefixCuts = s.prefixCuts + ts.length ∧
      queryCount tr ≤ queryCount tr₀ + ts.length * (N.card + 1) := by
  intro ts
  induction ts with
  | nil =>
    intro _ s hs hRs o tr₀
    exact ⟨[], s, tr₀, rfl, hs, subset_rfl, rfl, by simp, by simp, by simp, by simp⟩
  | cons t ts ih =>
    intro hw s hs hRs o tr₀
    obtain ⟨hw0, hw1⟩ := hw t (List.mem_cons_self ..)
    obtain ⟨p, s1, tr1, hpc, hs1, hsub1, hvp, hpal, -, hval, -⟩ :=
      prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1 V N i hi R hR s hs
        hRs _ hw0 hw1 o tr₀
    have hpv : R.ValidPos p := hvp.resolve_left hne
    have hpc1 := prefixCut_pc V N i R _ s o tr₀ p s1 tr1 hpc
    have hq1 := prefixCut_query_bound__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1
      V N i R _ s o tr₀ p s1 tr1 hpc
    obtain ⟨ps, s', tr, hr, h1, h2, h3, h4, h5, h6, h7⟩ :=
      ih (fun t' ht' => hw t' (List.mem_cons_of_mem _ ht')) s1 hs1 (aligned_mono s s1 hsub1 _ hRs) o tr1
    refine ⟨p :: ps, s', tr, ?_, h1, hsub1.trans h2, by simp [h3], ?_, ?_, ?_, ?_⟩
    · simp only [marksOf]
      rw [run_stbind, hpc]; dsimp only
      rw [run_stbind, hr]; rfl
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hpv, aligned_mono s1 s' h2 _ hpal⟩
      · exact h4 q hq
    · intro k hk
      cases k with
      | zero => simpa using hval
      | succ k => simpa using h5 k (by simpa using hk)
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; rw [Nat.add_mul, one_mul]; omega

theorem allMarks_ok {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) (R : Piece)
    (hR : R.WF) (hne : R ≠ []) (v : ι → ℝ) (M : ℕ) (hv : ∀ i ∈ N, v i = (V i).value R.toSet) :
    ∀ (l : List ι), (∀ i ∈ l, i ∈ N) →
    ∀ (s : Rec ι), s.Valid V N → s.Aligned R → ∀ (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
    ∃ (ms : List Pos) (s' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((allMarks N R v M l).run s) tr₀ = some ((ms, s'), tr) ∧
      s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ ms.length = l.length * (M - 1) ∧
      (∀ p ∈ ms, R.ValidPos p ∧ s'.Aligned (prefixList R p)) ∧
      (∀ i ∈ l, ∀ t, 1 ≤ t → t ≤ M - 1 → ∃ p ∈ ms,
        (V i).value (prefixList R p).toSet = (t : ℝ) * v i / M) ∧
      s'.prefixCuts = s.prefixCuts + l.length * (M - 1) ∧
      queryCount tr ≤ queryCount tr₀ + l.length * (M - 1) * (N.card + 1) := by
  intro l
  induction l with
  | nil =>
    intro _ s hs hRs o tr₀
    exact ⟨[], s, tr₀, rfl, hs, subset_rfl, by simp, by simp, by simp, by simp, by simp⟩
  | cons i l ih =>
    intro hl s hs hRs o tr₀
    have hi : i ∈ N := hl i (List.mem_cons_self ..)
    have hvR : 0 ≤ (V i).value R.toSet := value_nonneg _ (piece_measurable R)
    have hts : ∀ t ∈ List.range' 1 (M - 1), 0 ≤ (t : ℝ) * v i / M ∧ (t : ℝ) * v i / M ≤ (V i).value R.toSet := by
      intro t ht
      rw [List.mem_range'_1] at ht
      have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
      rw [hv i hi]
      refine ⟨by positivity, ?_⟩
      rw [div_le_iff₀ hM]
      have : (t : ℝ) ≤ M := by exact_mod_cast (show t ≤ M by omega)
      nlinarith
    obtain ⟨ps, s1, tr1, hr1, hs1, hsub1, hlen1, hps, hval1, hpc1, hq1⟩ :=
      marksOf_ok V N R hR hne i hi (v i) M _ hts s hs hRs o tr₀
    obtain ⟨qs, s', tr, hr, h1, h2, h3, h4, h5, h6, h7⟩ :=
      ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) s1 hs1 (aligned_mono s s1 hsub1 _ hRs) o tr1
    rw [List.length_range'] at hlen1
    refine ⟨ps ++ qs, s', tr, ?_, h1, hsub1.trans h2, by simp [hlen1, h3]; ring, ?_, ?_, ?_, ?_⟩
    · simp only [allMarks]
      rw [run_stbind, hr1]; dsimp only
      rw [run_stbind, hr]; rfl
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ⟨(hps p hp).1, aligned_mono s1 s' h2 _ (hps p hp).2⟩
      · exact h4 p hp
    · intro j hj t ht1 ht2
      rcases List.mem_cons.mp hj with rfl | hj
      · have hk : t - 1 < ps.length := by rw [hlen1]; omega
        refine ⟨ps[t - 1], List.mem_append_left _ (List.getElem_mem _), ?_⟩
        have := hval1 (t - 1) hk
        rw [this]
        congr 3
        rw [List.getD_eq_getElem?_getD, List.getElem?_range' (by omega)]
        simp; omega
      · obtain ⟨p, hp, hpv⟩ := h5 j hj t ht1 ht2
        exact ⟨p, List.mem_append_right _ hp, hpv⟩
    · simp only [List.length_cons, List.length_range'] at hpc1 ⊢; rw [h6, hpc1]; ring
    · simp only [List.length_cons, List.length_range'] at hq1 ⊢
      calc queryCount tr ≤ queryCount tr1 + l.length * (M - 1) * (N.card + 1) := h7
        _ ≤ queryCount tr₀ + (M - 1) * (N.card + 1) + l.length * (M - 1) * (N.card + 1) := by omega
        _ = queryCount tr₀ + (l.length + 1) * (M - 1) * (N.card + 1) := by ring
theorem value_biUnion_le (v : Valuation) (A : ℕ → Set ℝ) (hA : ∀ k, MeasurableSet (A k)) :
    ∀ s : Finset ℕ, v.value (⋃ k ∈ s, A k) ≤ ∑ k ∈ s, v.value (A k) := by
  intro s
  induction s using Finset.induction_on with
  | empty => simp [value_empty]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    have := value_union_le v (hA a) (Finset.measurableSet_biUnion s (fun k _ => hA k))
    linarith

open scoped Classical in
/-- The levels argument of Lemma 4 (p.12–13): no old bundle is cut. -/
theorem levels {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) (hN : 2 ≤ N.card)
    (cf : ℕ → Piece) (Q : ι → List ℕ) (D W : ι → Piece) (π : ι → ι)
    (hcd : ∀ c c', c ≠ c' → Disjoint (cf c).toSet (cf c').toSet)
    (hQnd : ∀ k ∈ N, (Q k).Nodup) (hlen : ∀ k ∈ N, (Q k).length = N.card - 1)
    (hDc : ∀ k ∈ N, ∀ c, Disjoint (D k).toSet (cf c).toSet)
    (hπ : Set.BijOn π (N : Set ι) (N : Set ι))
    (hsuf : ∀ a ∈ N, IsSuffix (W a).toSet (((Q (π a)).map cf).flatten ++ D (π a)))
    (hEF : EnvyFree V N (fun a => (W a).toSet))
    (hwhole : ∃ a ∈ N, (W a).toSet = Piece.toSet (((Q (π a)).map cf).flatten ++ D (π a)))
    (hii : ∀ S ⊆ N, S.Nonempty →
      (∀ a ∈ S, (W a).toSet ≠ Piece.toSet (((Q (π a)).map cf).flatten ++ D (π a))) →
      ∃ a ∈ S, ∃ b ∈ N, b ∉ S ∧ (V b).value (W a).toSet = (V b).value (W b).toSet)
    (hpair : ∀ i ∈ N, ∀ j ∈ N, ∀ r r', r < r' → r' < N.card - 1 →
      (V i).value (cf ((Q j).getD r' 0)).toSet ≤ (V i).value (cf ((Q i).getD r 0)).toSet)
    (hlast : ∀ i ∈ N, ∀ j ∈ N, (V i).value (D j).toSet <
      (V i).value (D i).toSet + (V i).value (cf ((Q i).getD (N.card - 2) 0)).toSet) :
    ∀ a ∈ N, (D (π a)).toSet ⊆ (W a).toSet := by
  set n := N.card with hn
  have hmeas : ∀ P : Piece, MeasurableSet P.toSet := piece_measurable
  haveI : Nonempty ι := by
    obtain ⟨x, _⟩ := Finset.card_pos.mp (show 0 < N.card by omega); exact ⟨x⟩
  let c : ι → ℕ → Set ℝ := fun k r => (cf ((Q k).getD r 0)).toSet
  -- the holder of each piece
  let σ : ι → ι := Function.invFunOn π (N : Set ι)
  have hσN : ∀ k ∈ N, σ k ∈ N := fun k hk => Function.invFunOn_mem (hπ.surjOn hk)
  have hπσ : ∀ k ∈ N, π (σ k) = k := fun k hk => Function.invFunOn_eq (hπ.surjOn hk)
  have hσπ : ∀ a ∈ N, σ (π a) = a := fun a ha => hπ.injOn (hσN _ (hπ.mapsTo ha)) ha
    (hπσ _ (hπ.mapsTo ha))
  -- blocks of each piece
  let BL : ι → List Piece := fun k => (Q k).map cf ++ [D k]
  have hBLlen : ∀ k ∈ N, (BL k).length = n := by
    intro k hk; simp [BL, hlen k hk]; omega
  have hBLflat : ∀ k, (BL k).flatten = ((Q k).map cf).flatten ++ D k := by
    intro k; simp [BL]
  have hBLget : ∀ k ∈ N, ∀ b, b < n - 1 → ((BL k).getD b []).toSet = c k b := by
    intro k hk b hb
    simp only [BL, c]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlen k hk]; omega),
      List.getElem?_map, List.getD_eq_getElem?_getD (l := Q k), List.getElem?_eq_getElem (by rw [hlen k hk]; omega)]
    simp
  have hBLD : ∀ k ∈ N, ((BL k).getD (n - 1) []).toSet = (D k).toSet := by
    intro k hk
    simp only [BL]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hlen k hk])]
    simp [hlen k hk]
  let S : ι → Set ℝ := fun k => (W (σ k)).toSet
  have hSsuf : ∀ k ∈ N, IsSuffix (S k) (BL k).flatten := by
    intro k hk
    have := hsuf (σ k) (hσN k hk)
    rw [hπσ k hk] at this; rw [hBLflat]; exact this
  -- from a non-contained block, the suffix lies in the later blocks
  have hlater : ∀ k ∈ N, ∀ b < n, ¬ ((BL k).getD b []).toSet ⊆ S k →
      S k ⊆ (D k).toSet ∪ ⋃ r ∈ Finset.Ico b (n - 1), c k r := by
    intro k hk b hb hnot y hy
    have := suffix_blocks (BL k) (S k) (hSsuf k hk) b (by rw [hBLlen k hk]; exact hb) hnot hy
    obtain ⟨b', hb', hyb'⟩ := Set.mem_iUnion₂.mp this
    rw [Finset.mem_Ico, hBLlen k hk] at hb'
    by_cases hb'n : b' = n - 1
    · subst hb'n; rw [hBLD k hk] at hyb'; exact Or.inl hyb'
    · rw [hBLget k hk b' (by omega)] at hyb'
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨b', Finset.mem_Ico.mpr ⟨hb'.1, by omega⟩, hyb'⟩)
  -- levels
  let good : ι → ℕ → Prop := fun k m => ∀ r, n - 1 - m ≤ r → r < n - 1 → c k r ⊆ S k
  let cnt : ι → ℕ := fun k => ((Finset.range n).filter (good k)).max' ⟨0, by
    simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, fun r h1 h2 => by omega⟩⟩
  have hcnt_mem : ∀ k, cnt k ∈ (Finset.range n).filter (good k) := fun k => Finset.max'_mem _ _
  have hcnt_lt : ∀ k, cnt k < n := fun k => Finset.mem_range.mp (Finset.mem_filter.mp (hcnt_mem k)).1
  have hcnt_good : ∀ k, good k (cnt k) := fun k => (Finset.mem_filter.mp (hcnt_mem k)).2
  have hcnt_max : ∀ k m, m < n → good k m → m ≤ cnt k := fun k m hm hg =>
    Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, hg⟩)
  let lvl : ι → ℕ := fun k => if (D k).toSet ⊆ S k then cnt k + 1 else 0
  have hlvl_le : ∀ k, lvl k ≤ n := fun k => by
    simp only [lvl]; split_ifs <;> have := hcnt_lt k <;> omega
  -- (U1)
  have hU1 : ∀ k, 1 ≤ lvl k → (D k).toSet ⊆ S k ∧
      ∀ r, n - lvl k ≤ r → r < n - 1 → c k r ⊆ S k := by
    intro k hk
    simp only [lvl] at hk ⊢
    split_ifs at hk ⊢ with hD
    · refine ⟨hD, fun r h1 h2 => hcnt_good k r (by omega) h2⟩
    · omega
  -- (U2)
  have hU2 : ∀ k ∈ N, lvl k ≤ n - 1 →
      S k ⊆ (D k).toSet ∪ ⋃ r ∈ Finset.Ico (n - 1 - lvl k) (n - 1), c k r := by
    intro k hk hl
    simp only [lvl] at hl ⊢
    split_ifs at hl ⊢ with hD
    · have hnot : ¬ good k (cnt k + 1) := fun hg => by
        have := hcnt_max k (cnt k + 1) (by omega) hg; omega
      simp only [good, not_forall] at hnot
      obtain ⟨r0, hr0a, hr0b, hr0⟩ := hnot
      have := hlater k hk r0 (by omega) (by rw [hBLget k hk r0 hr0b]; exact hr0)
      refine this.trans (Set.union_subset_union_right _ (Set.iUnion₂_subset fun r hr => ?_))
      exact Set.subset_iUnion₂ (s := fun r (_ : r ∈ Finset.Ico (n - 1 - (cnt k + 1)) (n - 1)) => c k r)
        r (Finset.mem_Ico.mpr ⟨by simp at hr; omega, (Finset.mem_Ico.mp hr).2⟩)
    · have := hlater k hk (n - 1) (by omega) (by rw [hBLD k hk]; exact hD)
      simpa using this
  -- (U4)
  have hU4 : ∀ a ∈ N, lvl (π a) < n →
      (W a).toSet ≠ Piece.toSet (((Q (π a)).map cf).flatten ++ D (π a)) := by
    intro a ha hl heq
    have hS : S (π a) = Piece.toSet (BL (π a)).flatten := by
      simp only [S, hσπ a ha, hBLflat]; exact heq
    have hall : ∀ b < n, ((BL (π a)).getD b []).toSet ⊆ S (π a) := by
      intro b hb
      rw [hS, toSet_flatten]
      exact Set.subset_biUnion_of_mem (u := fun b => ((BL (π a)).getD b []).toSet)
        (Finset.mem_range.mpr (by rw [hBLlen _ (hπ.mapsTo ha)]; exact hb))
    have hD : (D (π a)).toSet ⊆ S (π a) := by rw [← hBLD _ (hπ.mapsTo ha)]; exact hall (n - 1) (by omega)
    have hg : good (π a) (n - 1) := by
      intro r _ hr; rw [← hBLget _ (hπ.mapsTo ha) r hr]; exact hall r (by omega)
    have := hcnt_max (π a) (n - 1) (by omega) hg
    simp only [lvl, if_pos hD] at hl; omega
  -- values
  have hmc : ∀ k r, MeasurableSet (c k r) := fun k r => hmeas _
  have hVnn : ∀ i k r, 0 ≤ (V i).value (c k r) := fun i k r => value_nonneg _ (hmc k r)
  have hstrict : ∀ i ∈ N, ∀ j ∈ N, lvl j + 2 ≤ lvl i → (V i).value (S j) < (V i).value (S i) := by
    intro i hi j hj hl
    have hlj : lvl j ≤ n - 2 := by have := hlvl_le i; omega
    have h1 := value_mono (V i) (hU2 j hj (by omega))
      ((hmeas _).union (Finset.measurableSet_biUnion _ (fun r _ => hmc j r)))
    have h2 := value_union_le (V i) (hmeas (D j)) (Finset.measurableSet_biUnion
      (Finset.Ico (n - 1 - lvl j) (n - 1)) (fun r _ => hmc j r))
    have h3 := value_biUnion_le (V i) (c j) (hmc j) (Finset.Ico (n - 1 - lvl j) (n - 1))
    -- round robin: shift indices by one
    have h4 : ∑ r ∈ Finset.Ico (n - 1 - lvl j) (n - 1), (V i).value (c j r) ≤
        ∑ r ∈ Finset.Ico (n - 1 - lvl j) (n - 1), (V i).value (c i (r - 1)) := by
      apply Finset.sum_le_sum; intro r hr
      rw [Finset.mem_Ico] at hr
      exact hpair i hi j hj (r - 1) r (by omega) (by omega)
    have h5 : ∑ r ∈ Finset.Ico (n - 1 - lvl j) (n - 1), (V i).value (c i (r - 1)) =
        ∑ r ∈ Finset.Ico (n - 2 - lvl j) (n - 2), (V i).value (c i r) := by
      apply Finset.sum_nbij' (fun r => r - 1) (fun r => r + 1)
      · intro r hr; simp only [Finset.mem_coe, Finset.mem_Ico] at hr ⊢; omega
      · intro r hr; simp only [Finset.mem_coe, Finset.mem_Ico] at hr ⊢; omega
      · intro r hr; simp only [Finset.mem_coe, Finset.mem_Ico] at hr; omega
      · intro r _; simp
      · intro r _; rfl
    have h6 : ∑ r ∈ Finset.Ico (n - 2 - lvl j) (n - 2), (V i).value (c i r) ≤
        ∑ r ∈ Finset.Ico (n - lvl i) (n - 2), (V i).value (c i r) :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => by
        simp only [Finset.mem_Ico] at hr ⊢; omega) (fun r _ _ => hVnn i i r)
    have h7 := hlast i hi j hj
    have h8 : ∑ r ∈ Finset.Ico (n - lvl i) (n - 2), (V i).value (c i r) +
        (V i).value (c i (n - 2)) = ∑ r ∈ Finset.Ico (n - lvl i) (n - 1), (V i).value (c i r) := by
      rw [show n - 1 = (n - 2) + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
    -- the right-hand side is contained in `S i`
    obtain ⟨hDi, hci⟩ := hU1 i (by omega)
    have hdisjc : ∀ r ∈ Finset.Ico (n - lvl i) (n - 1), ∀ r' ∈ Finset.Ico (n - lvl i) (n - 1),
        r ≠ r' → Disjoint (c i r) (c i r') := by
      intro r hr r' hr' hrr'
      apply hcd
      intro h
      have hr1 : r < (Q i).length := by rw [hlen i hi]; simp at hr; omega
      have hr2 : r' < (Q i).length := by rw [hlen i hi]; simp at hr'; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr1, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hr2] at h
      exact hrr' ((hQnd i hi).getElem_inj_iff.mp (by simpa using h))
    have h9 : (V i).value ((D i).toSet ∪ ⋃ r ∈ Finset.Ico (n - lvl i) (n - 1), c i r) =
        (V i).value (D i).toSet + ∑ r ∈ Finset.Ico (n - lvl i) (n - 1), (V i).value (c i r) := by
      rw [value_union _ (Finset.measurableSet_biUnion _ (fun r _ => hmc i r))
        (by rw [Set.disjoint_iUnion₂_right]; intro r _; exact hDc i hi _),
        value_biUnion (V i) (c i) _ (fun r _ => hmc i r) hdisjc]
    have h10 := value_mono (V i) (Set.union_subset hDi (Set.iUnion₂_subset fun r hr =>
      hci r (Finset.mem_Ico.mp hr).1 (Finset.mem_Ico.mp hr).2)) (hmeas _)
    linarith
  -- if an old bundle were cut ...
  intro a0 ha0
  by_contra hcut
  have hk0 : lvl (π a0) = 0 := by simp only [lvl]; rw [if_neg (by simpa [S, hσπ a0 ha0] using hcut)]
  obtain ⟨a1, ha1, hwh⟩ := hwhole
  have hk1 : lvl (π a1) = n := by
    by_contra h
    exact hU4 a1 ha1 (by have := hlvl_le (π a1); omega) hwh
  -- a missing level
  obtain ⟨lam, hlam1, hlamn, hlam⟩ : ∃ lam, 1 ≤ lam ∧ lam ≤ n - 1 ∧ ∀ k ∈ N, lvl k ≠ lam := by
    by_contra hcon
    push Not at hcon
    choose f hfN hf using hcon
    let F : ℕ → ι := fun l => if h : 1 ≤ l ∧ l ≤ n - 1 then f l h.1 h.2 else π a0
    have hcard := Finset.card_le_card_of_injOn (s := Finset.Icc 1 (n - 1))
      (t := (N.erase (π a0)).erase (π a1)) F
      (fun l hl => by
        have hl' : 1 ≤ l ∧ l ≤ n - 1 := by simpa using hl
        simp only [F, dif_pos hl']
        refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hfN l hl'.1 hl'.2⟩⟩)
        · intro h; have := hf l hl'.1 hl'.2; rw [h, hk1] at this; omega
        · intro h; have := hf l hl'.1 hl'.2; rw [h, hk0] at this; omega)
      (by
        intro l₁ hl₁ l₂ hl₂ he
        have h1 : 1 ≤ l₁ ∧ l₁ ≤ n - 1 := by simpa using hl₁
        have h2 : 1 ≤ l₂ ∧ l₂ ≤ n - 1 := by simpa using hl₂
        simp only [F, dif_pos h1, dif_pos h2] at he
        have e1 := hf l₁ h1.1 h1.2; have e2 := hf l₂ h2.1 h2.2
        rw [he] at e1; rw [e1] at e2; exact e2)
    have hne : π a1 ≠ π a0 := by intro h; rw [h, hk0] at hk1; omega
    rw [Nat.card_Icc, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne, hπ.mapsTo ha1⟩),
      Finset.card_erase_of_mem (hπ.mapsTo ha0)] at hcard
    omega
  let H := N.filter (fun k => lam < lvl k)
  let Lo := N.filter (fun k => lvl k < lam)
  -- agents of `H` hold pieces of `H`
  have hHH : ∀ a ∈ H, π a ∈ H := by
    intro a haH
    obtain ⟨haN, hal⟩ := Finset.mem_filter.mp haH
    by_contra hpa
    have hpaN := hπ.mapsTo haN
    have hlo : lvl (π a) < lam := by
      have := hlam (π a) hpaN
      have : ¬ lam < lvl (π a) := fun h => hpa (Finset.mem_filter.mpr ⟨hpaN, h⟩)
      omega
    have hs := hstrict a haN (π a) hpaN (by omega)
    have hW : S (π a) = (W a).toSet := by simp only [S, hσπ a haN]
    have hEFa := hEF a haN (σ a) (hσN a haN)
    simp only [S] at hs hW
    rw [hW] at hs
    exact absurd hEFa (not_le.mpr hs)
  have hLoLo : ∀ b ∈ Lo, π b ∈ Lo := by
    intro b hbLo
    obtain ⟨hbN, hbl⟩ := Finset.mem_filter.mp hbLo
    have hpbN := hπ.mapsTo hbN
    have hnotH : π b ∉ H := by
      intro hpbH
      -- π maps H onto H
      have himg : H.image π = H := by
        apply Finset.eq_of_subset_of_card_le
        · intro y hy; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy; exact hHH a ha
        · rw [Finset.card_image_of_injOn (fun x hx y hy h => hπ.injOn
            (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 h)]
      rw [← himg] at hpbH
      obtain ⟨a, haH, hab⟩ := Finset.mem_image.mp hpbH
      have := hπ.injOn (Finset.mem_filter.mp haH).1 hbN hab
      subst this
      have := (Finset.mem_filter.mp haH).2; omega
    have := hlam (π b) hpbN
    have : ¬ lam < lvl (π b) := fun h => hnotH (Finset.mem_filter.mpr ⟨hpbN, h⟩)
    exact Finset.mem_filter.mpr ⟨hpbN, by omega⟩
  -- property (ii) of Lemma 6
  have hLone : Lo.Nonempty :=
    ⟨π a0, Finset.mem_filter.mpr ⟨hπ.mapsTo ha0, by rw [hk0]; omega⟩⟩
  obtain ⟨b, hbLo, j, hjN, hjLo, heq⟩ := hii Lo (Finset.filter_subset _ _) hLone (by
    intro b hbLo
    have hpb := Finset.mem_filter.mp (hLoLo b hbLo)
    exact hU4 b (Finset.mem_filter.mp hbLo).1 (by omega))
  have hbN := (Finset.mem_filter.mp hbLo).1
  have hjH : lam < lvl j := by
    have := hlam j hjN
    have : ¬ lvl j < lam := fun h => hjLo (Finset.mem_filter.mpr ⟨hjN, h⟩)
    omega
  have hpb := (Finset.mem_filter.mp (hLoLo b hbLo)).2
  have hs := hstrict j hjN (π b) (hπ.mapsTo hbN) (by omega)
  have hW : S (π b) = (W b).toSet := by simp only [S, hσπ b hbN]
  have hEFj := hEF j hjN (σ j) (hσN j hjN)
  simp only [S] at hs hW
  rw [hW] at hs
  simp only at hEFj
  linarith
theorem value_listUnion_le (v : Valuation) (cf : ℕ → Piece) :
    ∀ l : List ℕ, v.value (⋃ c ∈ l, (cf c).toSet) ≤ (l.map (fun c => v.value (cf c).toSet)).sum
  | [] => by simp [value_empty]
  | a :: l => by
    have h : (⋃ c ∈ a :: l, (cf c).toSet) = (cf a).toSet ∪ ⋃ c ∈ l, (cf c).toSet := by
      ext y; simp
    rw [h, List.map_cons, List.sum_cons]
    refine (value_union_le v (piece_measurable _) ?_).trans
      (add_le_add le_rfl (value_listUnion_le v cf l))
    rw [← toSet_flatten_map]; exact piece_measurable _

theorem finset_list_sum (L : ℕ) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.range L, g k = ((List.range L).map g).sum := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

set_option maxHeartbeats 4000000 in
open scoped Classical in
theorem lemma4_main {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 2 ≤ N.card) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / (6 * (N.card : ℝ) ^ 3))
    (D : ι → Piece) (R : Piece) (hD : ∀ i ∈ N, (D i).WF) (hR : R.WF)
    (hDdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (D i).toSet (D j).toSet)
    (hDR : ∀ i ∈ N, Disjoint (D i).toSet R.toSet)
    (hpos : ∀ i ∈ N, 0 < (V i).value R.toSet)
    (halmost : ∀ i ∈ N, ∀ j ∈ N,
      (V i).value (D j).toSet - ε * (V i).value R.toSet ≤ (V i).value (D i).toSet)
    (s : Rec ι) (hs : s.Valid V N) (hDs : ∀ i ∈ N, s.Aligned (D i)) (hRs : s.Aligned R)
    (o : ChoiceOracle ι) :
    ∃ (W : ι → Piece) (U : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (repair N D R ε) s = some ((W, U), s', tr) ∧
      EnvyFree V N (fun i => (W i).toSet) ∧
      (∃ (σ : ι → ι) (Z : ι → Set ℝ), Set.BijOn σ (N : Set ι) (N : Set ι) ∧
        (∀ j ∈ N, Z j ⊆ R.toSet) ∧
        (∀ j ∈ N, ∀ k ∈ N, j ≠ k → Disjoint (Z j) (Z k)) ∧
        (∀ j ∈ N, (W (σ j)).toSet = (D j).toSet ∪ Z j) ∧
        (∀ i ∈ N, ∀ j ∈ N,
          (V i).value (Z j) ≤ 3 * (N.card : ℝ) ^ 2 * ε * (V i).value R.toSet) ∧
        U.toSet = R.toSet \ ⋃ j ∈ N, Z j) ∧
      (queryCount tr : ℝ) ≤ (N.card : ℝ) / ε + (N.card : ℝ) ^ 3 * ((N.card.factorial : ℝ)) ^ 2 := by
  have hmeas : ∀ P : Piece, MeasurableSet P.toSet := piece_measurable
  have hrec : ∀ t : Rec ι, t.Valid V N → ∀ i ∈ N, ∀ P : Piece, P.WF → t.Aligned P →
      t.pieceVal i P = (V i).value P.toSet := fun t ht i hi P hP hPa =>
    recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 V N t ht i hi P hP hPa
  obtain ⟨i0, hi0⟩ : N.Nonempty := Finset.card_pos.mp (by omega)
  have hne : R ≠ [] := by
    intro h; have := hpos i0 hi0; rw [h, toSet_nil, value_empty] at this; linarith
  have hnR : (2 : ℝ) ≤ N.card := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N.card := by linarith
  -- the number of parts M
  have hM1 : 1 / (3 * (N.card : ℝ) * ε) ≤ (⌈1 / (3 * (N.card : ℝ) * ε)⌉₊ : ℝ) := Nat.le_ceil _
  have hM2 : (⌈1 / (3 * (N.card : ℝ) * ε)⌉₊ : ℝ) < 1 / (3 * (N.card : ℝ) * ε) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h6 : 6 * (N.card : ℝ) ^ 3 * ε ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hε'; linarith
  have hbig : 2 * (N.card : ℝ) ^ 2 ≤ 1 / (3 * (N.card : ℝ) * ε) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hMn : N.card ≤ ⌈1 / (3 * (N.card : ℝ) * ε)⌉₊ := by
    have : (N.card : ℝ) ≤ ⌈1 / (3 * (N.card : ℝ) * ε)⌉₊ := by nlinarith
    exact_mod_cast this
  set M := ⌈1 / (3 * (N.card : ℝ) * ε)⌉₊ with hMdef
  -- Line 1: marks and cells
  obtain ⟨ms, s1, tr1, hmk, hs1, hsub1, hmslen, hmsp, hgrid, hpc1, hq1⟩ :=
    allMarks_ok V N R hR hne (fun i => s.pieceVal i R) M (fun i hi => hrec s hs i hi R hR hRs)
      N.toList (fun i hi => Finset.mem_toList.mp hi) s hs hRs o []
  rw [Finset.length_toList] at hmslen hpc1 hq1
  have hRs1 : s1.Aligned R := aligned_mono s s1 hsub1 _ hRs
  set cells := cellsOf R ms with hcells
  obtain ⟨hcwa, hcd, hcU⟩ := cells_facts R hR s1 hRs1 ms (fun _ => hmsp)
  obtain ⟨hclen, hck, hbmono, hb0, hbend, hbgrid⟩ := cellsOf_spec R hR hne s1 hRs1 ms
    (fun p hp => (hmsp p hp).1) (fun p hp => (hmsp p hp).2)
  let cf : ℕ → Piece := fun c => cells.getD c []
  have hcR : ∀ k, (cf k).toSet ⊆ R.toSet := by
    intro k
    by_cases hk : k < cells.length
    · rw [← hcU]; exact Set.subset_biUnion_of_mem (u := fun k => (cells.getD k []).toSet)
        (Finset.mem_range.mpr hk)
    · simp only [cf]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      simp [toSet_nil]
  -- the agent order and round robin
  have hpermne : N.toList.permutations ≠ [] :=
    List.ne_nil_of_mem (List.mem_permutations.mpr (List.Perm.refl _))
  obtain ⟨order, hordm, tr2, hord, hq2⟩ := run_choose_ex V o N.toList.permutations hpermne s1 tr1
  rw [List.mem_permutations] at hordm
  have hordnd : order.Nodup := hordm.nodup_iff.mpr (Finset.nodup_toList N)
  have hordN : ∀ i, i ∈ order ↔ i ∈ N := fun i => by rw [hordm.mem_iff, Finset.mem_toList]
  have hordlen : order.length = N.card := by rw [hordm.length_eq, Finset.length_toList]
  have hL : cells.length = N.card * (M - 1) + 1 := by rw [hclen, hmslen]
  have hI0 : RRI cells order s1 cells.length (fun _ => []) (List.range cells.length) := by
    refine ⟨by simp, fun i _ c hc => by simp at hc, fun i _ j _ r r' _ hr' => by simp at hr'⟩
  obtain ⟨Q, avail, tr3, hrr, hq3, ⟨hperm, hdom, hpair⟩, hQlen⟩ :=
    roundRobin_fwd V cells order hordnd s1 cells.length (N.card - 1) 0 (List.range cells.length)
      (fun _ => []) o tr2 hI0 (by simp) (by
        rw [List.length_range, hL, hordlen]
        have : N.card - 1 ≤ M - 1 := by omega
        nlinarith)
  have hQlenN : ∀ i ∈ N, (Q i).length = N.card - 1 := fun i hi => by
    rw [hQlen i ((hordN i).mpr hi)]; simp
  -- the picked indices
  have hnd := hperm.nodup_iff.mpr List.nodup_range
  rw [List.nodup_append] at hnd
  obtain ⟨hndF, hndA, hdisjFA⟩ := hnd
  rw [List.nodup_flatten] at hndF
  obtain ⟨hndQ, hpw⟩ := hndF
  have hQnd : ∀ i ∈ N, (Q i).Nodup := fun i hi =>
    hndQ _ (List.mem_map.mpr ⟨i, (hordN i).mpr hi, rfl⟩)
  have hQdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → ∀ c ∈ Q i, c ∉ Q j := by
    intro i hi j hj hij c hci hcj
    rw [List.pairwise_map] at hpw
    haveI : Std.Symm (fun a b => (Q a).Disjoint (Q b)) := ⟨fun a b h => h.symm⟩
    exact hpw.forall ((hordN i).mpr hi) ((hordN j).mpr hj) hij hci hcj
  have hQavail : ∀ i ∈ N, ∀ c ∈ Q i, c ∉ avail := by
    intro i hi c hci hca
    exact hdisjFA c (List.mem_flatten.mpr ⟨Q i, List.mem_map.mpr ⟨i, (hordN i).mpr hi, rfl⟩, hci⟩)
      c hca rfl
  have hcover : ∀ c, c < cells.length → c ∈ avail ∨ ∃ i ∈ N, c ∈ Q i := by
    intro c hc
    have : c ∈ (order.map Q).flatten ++ avail := hperm.mem_iff.mpr (List.mem_range.mpr hc)
    rcases List.mem_append.mp this with h | h
    · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp h
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
      exact Or.inr ⟨i, (hordN i).mp hi, hcl⟩
    · exact Or.inl h
  have hcf_wf : ∀ c, (cf c).WF := fun c => (hcwa c).1
  have hcf_al : ∀ c, s1.Aligned (cf c) := fun c => (hcwa c).2
  have hcf_d : ∀ c c', c ≠ c' → Disjoint (cf c).toSet (cf c').toSet := hcd
  -- the pieces passed to Permute
  let P : ι → Piece := fun i => ((Q i).map cf).flatten ++ D i
  have hPset : ∀ i, (P i).toSet = (⋃ c ∈ Q i, (cf c).toSet) ∪ (D i).toSet := fun i => by
    simp only [P, toSet_append, toSet_flatten_map]
  have hflatR : ∀ l : List ℕ, (⋃ c ∈ l, (cf c).toSet) ⊆ R.toSet :=
    fun l => Set.iUnion₂_subset (fun c _ => hcR c)
  have hPwf : ∀ i ∈ N, (P i).WF := fun i hi =>
    wf_append _ _ (flat_wf cf hcf_wf hcf_d _ (hQnd i hi)) (hD i hi)
      (by rw [toSet_flatten_map]; exact Disjoint.mono_left (hflatR _) (hDR i hi).symm)
  have hPal : ∀ i ∈ N, s1.Aligned (P i) := fun i hi =>
    aligned_append s1 _ _ (flat_aligned s1 cf hcf_al _) (aligned_mono s s1 hsub1 _ (hDs i hi))
  have hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet := by
    intro i hi j hj hij
    rw [hPset, hPset]
    refine Disjoint.union_left (Disjoint.union_right ?_ ?_) (Disjoint.union_right ?_ (hDdisj i hi j hj hij))
    · rw [Set.disjoint_iUnion₂_left]; intro c hc
      rw [Set.disjoint_iUnion₂_right]; intro c' hc'
      exact hcf_d c c' (fun h => hQdisj i hi j hj hij c hc (h ▸ hc'))
    · exact Disjoint.mono_left (hflatR _) (hDR j hj).symm
    · exact Disjoint.mono_right (hflatR _) (hDR i hi)
  -- Line 8: Permute
  obtain ⟨W, U0, s2, tc4, hex6, hEFW, hres6, ⟨π, hπ, hsuf, hwhole, hii⟩, hpc6⟩ :=
    EnvyFreeCake104.Divide.lemma_6 V N ⟨i0, hi0⟩ P hPwf hPdisj s1 hs1 hPal (fun t m ↦ o (tr3 ++ t) m)
  have hrun6 := run_from_exec V o _ s1 tr3 _ s2 tc4 hex6
  have hq6 := permute_query_meter__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2 V N P s1 _ W U0 s2 tc4 hex6
  -- the run of Repair
  have hexec : exec V o (repair N D R ε) s =
      some ((W, (avail.map cf).flatten ++ U0), s2, tr3 ++ tc4) := by
    rw [exec_iff]
    unfold repair
    rw [run_stbind, run_get']; dsimp only
    rw [run_stbind, hmk]; dsimp only
    rw [run_stbind, hord]; dsimp only
    rw [run_stbind, hrr]; dsimp only
    rw [run_stbind, hrun6]; dsimp only
    rw [run_pure']
  -- values of cells
  have hMpos : (0 : ℝ) < M := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    linarith
  have hrec1 : ∀ i ∈ N, ∀ c, s1.pieceVal i (cells.getD c []) = (V i).value (cf c).toSet :=
    fun i hi c => hrec s1 hs1 i hi _ (hcf_wf c) (hcf_al c)
  have hcv : ∀ i ∈ N, ∀ k, (V i).value (cf k).toSet ≤ (V i).value R.toSet / M := by
    intro i hi k
    by_cases hk : k ≤ ms.length
    · have hbm : ∀ j, MeasurableSet (bnd R ((0, (R.getD 0 default).a) :: ms.mergeSort posLE) j) := by
        intro j; unfold bnd; split_ifs
        · exact hmeas _
        · exact hmeas _
      let f : ℕ → ℝ := fun j => (V i).value (bnd R ((0, (R.getD 0 default).a) :: ms.mergeSort posLE) j)
      have hstep := small_steps f ms.length M ((V i).value R.toSet) (by omega)
        (fun j j' hjj' _ => value_mono _ (hbmono j j' hjj') (hbm j'))
        (by simp only [f]; rw [hb0, value_empty])
        (by simp only [f]; rw [hbend])
        (by
          intro t ht1 ht2
          obtain ⟨p, hp, hpv⟩ := hgrid i (Finset.mem_toList.mpr hi) t ht1 ht2
          obtain ⟨j, hj, hjp⟩ := hbgrid p hp
          refine ⟨j, hj, ?_⟩
          simp only [f]; rw [hjp, hpv, hrec s hs i hi R hR hRs]) k hk
      have hcell := (hck k hk).2.2
      have : (V i).value (cf k).toSet = f (k + 1) - f k := by
        simp only [cf, f]; rw [hcell]
        exact value_sdiff _ (hbm _) (hbm _) (hbmono k (k + 1) (by omega))
      rw [this]; exact hstep
    · have : cf k = [] := by
        simp only [cf]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [this, toSet_nil, value_empty]
      exact div_nonneg (value_nonneg _ (hmeas R)) hMpos.le
  have hMε : (N.card : ℝ) * (N.card - 1) / M ≤ 1 / 2 := by
    rw [div_le_iff₀ hMpos]
    have : 3 * (N.card : ℝ) ^ 3 * ε ≤ 1 / 2 := by linarith
    have hM1' : 1 ≤ 3 * (N.card : ℝ) * ε * M := by
      have := hM1; rw [div_le_iff₀ (by positivity)] at this; linarith
    nlinarith
  -- the last pick is worth more than ε V_i(R)
  have hlastpick : ∀ i ∈ N, ε * (V i).value R.toSet <
      (V i).value (cf ((Q i).getD (N.card - 2) 0)).toSet := by
    intro i hi
    have hio := (hordN i).mpr hi
    set cstar := (Q i).getD (N.card - 2) 0
    have hcs : cstar ∈ Q i := by
      simp only [cstar]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hQlenN i hi]; omega)]
      exact List.getElem_mem _
    have hdomi : ∀ c ∈ avail, (V i).value (cf c).toSet ≤ (V i).value (cf cstar).toSet := by
      intro c hc
      have := hdom i hio cstar hcs c hc
      rwa [hrec1 i hi, hrec1 i hi] at this
    let g : ℕ → ℝ := fun c => (V i).value (cf c).toSet
    have hVR : (V i).value R.toSet = ((List.range cells.length).map g).sum := by
      rw [← hcU, value_biUnion (V i) _ _ (fun k _ => hmeas _) (fun k _ k' _ h => hcd k k' h)]
      exact finset_list_sum cells.length g
    have hsplit : ((List.range cells.length).map g).sum =
        (((order.map Q).flatten).map g).sum + (avail.map g).sum := by
      rw [← List.sum_append, ← List.map_append]; exact (hperm.map g).sum_eq.symm
    have hflen : ((order.map Q).flatten).length = N.card * (N.card - 1) := by
      rw [List.length_flatten, List.map_map]
      have : order.map (List.length ∘ Q) = order.map (fun _ => N.card - 1) :=
        List.map_congr_left (fun i hi => by simp [hQlenN i ((hordN i).mp hi)])
      rw [this, List.map_const', List.sum_replicate, hordlen, smul_eq_mul]
    by_contra hcon
    push_neg at hcon
    have hVpos := hpos i hi
    have hA : (avail.map g).sum ≤ avail.length * (ε * (V i).value R.toSet) := by
      have := List.sum_le_card_nsmul (avail.map g) (ε * (V i).value R.toSet) (by
        intro x hx; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx; exact (hdomi c hc).trans hcon)
      rw [List.length_map, nsmul_eq_mul] at this; exact this
    have hF : (((order.map Q).flatten).map g).sum ≤
        ((N.card * (N.card - 1) : ℕ) : ℝ) * ((V i).value R.toSet / M) := by
      have := List.sum_le_card_nsmul (((order.map Q).flatten).map g) ((V i).value R.toSet / M) (by
        intro x hx; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx; exact hcv i hi c)
      rw [List.length_map, hflen, nsmul_eq_mul] at this; exact this
    have hlenA : avail.length ≤ N.card * M := by
      have h1 := hperm.length_eq
      rw [List.length_append, List.length_range] at h1
      have h2 : N.card * (M - 1) + N.card = N.card * M := by
        rw [← Nat.mul_succ]; congr 1; omega
      omega
    have hAlen : (avail.length : ℝ) * ε < 1 / 2 := by
      have h1 : (avail.length : ℝ) ≤ N.card * M := by exact_mod_cast hlenA
      have hk : (N.card : ℝ) * ε * (1 / (3 * N.card * ε)) = 1 / 3 := by field_simp
      have h3 : (N.card : ℝ) * ε * M < (N.card : ℝ) * ε * (1 / (3 * N.card * ε) + 1) :=
        mul_lt_mul_of_pos_left hM2 (by positivity)
      have h4 : (N.card : ℝ) * ε ≤ 1 / 24 := by
        have hn2 : (4 : ℝ) ≤ (N.card : ℝ) ^ 2 := by nlinarith
        have h5 := mul_le_mul_of_nonneg_right hn2 (show (0 : ℝ) ≤ 6 * (N.card : ℝ) * ε by positivity)
        have h7 : (N.card : ℝ) ^ 2 * (6 * (N.card : ℝ) * ε) = 6 * (N.card : ℝ) ^ 3 * ε := by ring
        linarith
      nlinarith
    have hcast : ((N.card * (N.card - 1) : ℕ) : ℝ) = (N.card : ℝ) * (N.card - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]; simp
    rw [hcast] at hF
    have hF' : (((order.map Q).flatten).map g).sum ≤ (V i).value R.toSet / 2 := by
      calc _ ≤ _ := hF
        _ = ((N.card : ℝ) * (N.card - 1) / M) * (V i).value R.toSet := by ring
        _ ≤ (1 / 2) * (V i).value R.toSet := mul_le_mul_of_nonneg_right hMε hVpos.le
        _ = _ := by ring
    have hA' : (avail.map g).sum < (V i).value R.toSet / 2 := by
      calc _ ≤ _ := hA
        _ = ((avail.length : ℝ) * ε) * (V i).value R.toSet := by ring
        _ < (1 / 2) * (V i).value R.toSet := mul_lt_mul_of_pos_right hAlen hVpos
        _ = _ := by ring
    have := hVR.trans hsplit
    linarith
  have hlast : ∀ i ∈ N, ∀ j ∈ N, (V i).value (D j).toSet <
      (V i).value (D i).toSet + (V i).value (cf ((Q i).getD (N.card - 2) 0)).toSet := by
    intro i hi j hj
    linarith [halmost i hi j hj, hlastpick i hi]
  have hpair' : ∀ i ∈ N, ∀ j ∈ N, ∀ r r', r < r' → r' < N.card - 1 →
      (V i).value (cf ((Q j).getD r' 0)).toSet ≤ (V i).value (cf ((Q i).getD r 0)).toSet := by
    intro i hi j hj r r' hrr' hr'
    have h1 : r' < (Q j).length := by rw [hQlenN j hj]; exact hr'
    have h2 : r < (Q i).length := by rw [hQlenN i hi]; omega
    have := hpair i ((hordN i).mpr hi) j ((hordN j).mpr hj) r r' hrr' h1 h2
    rw [hrec1 i hi, hrec1 i hi] at this
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some,
      List.getD_eq_getElem?_getD (l := Q i), List.getElem?_eq_getElem h2, Option.getD_some]
  have hDc : ∀ k ∈ N, ∀ c, Disjoint (D k).toSet (cf c).toSet := fun k hk c =>
    Disjoint.mono_right (hcR c) (hDR k hk)
  have hDW := levels V N hN cf Q D W π hcf_d hQnd hQlenN hDc hπ hsuf hEFW hwhole hii hpair' hlast
  -- the bijection σ and the extra pieces Z
  haveI : Nonempty ι := ⟨i0⟩
  let σ : ι → ι := Function.invFunOn π (N : Set ι)
  have hσN : ∀ k ∈ N, σ k ∈ N := fun k hk => Function.invFunOn_mem (hπ.surjOn hk)
  have hπσ : ∀ k ∈ N, π (σ k) = k := fun k hk => Function.invFunOn_eq (hπ.surjOn hk)
  have hσπ : ∀ a ∈ N, σ (π a) = a := fun a ha => hπ.injOn (hσN _ (hπ.mapsTo ha)) ha
    (hπσ _ (hπ.mapsTo ha))
  have hσ : Set.BijOn σ (N : Set ι) (N : Set ι) := by
    refine ⟨fun k hk => hσN k hk, fun a ha b hb hab => ?_, fun a ha => ⟨π a, hπ.mapsTo ha, hσπ a ha⟩⟩
    rw [← hπσ a ha, ← hπσ b hb, hab]
  have hWP : ∀ a ∈ N, (W a).toSet ⊆ (P (π a)).toSet := fun a ha => suffix_sub_piece _ _ (hsuf a ha)
  let Z : ι → Set ℝ := fun j => (W (σ j)).toSet \ (D j).toSet
  have hZW : ∀ j ∈ N, (W (σ j)).toSet = (D j).toSet ∪ Z j := by
    intro j hj
    have := hDW (σ j) (hσN j hj)
    rw [hπσ j hj] at this
    exact (Set.union_diff_cancel this).symm
  have hZQ : ∀ j ∈ N, Z j ⊆ ⋃ c ∈ Q j, (cf c).toSet := by
    intro j hj y ⟨hyW, hyD⟩
    have := hWP (σ j) (hσN j hj) hyW
    rw [hπσ j hj, hPset] at this
    rcases this with h | h
    · exact h
    · exact absurd h hyD
  have hZR : ∀ j ∈ N, Z j ⊆ R.toSet := fun j hj => (hZQ j hj).trans (hflatR _)
  have hZP : ∀ j ∈ N, Z j ⊆ (P j).toSet := fun j hj y hy => by
    rw [hPset]; exact Or.inl (hZQ j hj hy)
  have hZd : ∀ j ∈ N, ∀ k ∈ N, j ≠ k → Disjoint (Z j) (Z k) := fun j hj k hk hjk =>
    Disjoint.mono (hZP j hj) (hZP k hk) (hPdisj j hj k hk hjk)
  have hZv : ∀ i ∈ N, ∀ j ∈ N, (V i).value (Z j) ≤ 3 * (N.card : ℝ) ^ 2 * ε * (V i).value R.toSet := by
    intro i hi j hj
    have hVnn : 0 ≤ (V i).value R.toSet := value_nonneg _ (hmeas R)
    have h1 : (V i).value (Z j) ≤ (V i).value (⋃ c ∈ Q j, (cf c).toSet) :=
      value_mono _ (hZQ j hj) (by rw [← toSet_flatten_map]; exact hmeas _)
    have h2 := value_listUnion_le (V i) cf (Q j)
    have h3 := List.sum_le_card_nsmul ((Q j).map (fun c => (V i).value (cf c).toSet))
      ((V i).value R.toSet / M) (by
        intro x hx; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx; exact hcv i hi c)
    rw [List.length_map, hQlenN j hj, nsmul_eq_mul] at h3
    have hcast : ((N.card - 1 : ℕ) : ℝ) = (N.card : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcast] at h3
    have hM1' : 1 ≤ 3 * (N.card : ℝ) * ε * M := by
      have := hM1; rw [div_le_iff₀ (mul_pos (mul_pos (by norm_num) hnpos) hε)] at this; linarith
    have h4 : ((N.card : ℝ) - 1) * ((V i).value R.toSet / M) ≤
        3 * (N.card : ℝ) ^ 2 * ε * (V i).value R.toSet := by
      rw [mul_div_assoc', div_le_iff₀ hMpos]
      have h5 : ((N.card : ℝ) - 1) * (V i).value R.toSet ≤ (N.card : ℝ) * (V i).value R.toSet :=
        mul_le_mul_of_nonneg_right (by linarith) hVnn
      have h6 : (N.card : ℝ) * (V i).value R.toSet ≤
          (N.card : ℝ) * (V i).value R.toSet * (3 * (N.card : ℝ) * ε * M) :=
        le_mul_of_one_le_right (mul_nonneg hnpos.le hVnn) hM1'
      nlinarith
    linarith
  -- the residue
  have hres : Piece.toSet ((avail.map cf).flatten ++ U0) = R.toSet \ ⋃ j ∈ N, Z j := by
    rw [toSet_append, toSet_flatten_map, hres6]
    ext y
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and]
    constructor
    · rintro (⟨c, hc, hy⟩ | ⟨⟨i, hi, hyP⟩, hyW⟩)
      · refine ⟨hcR c hy, fun j hj hyZ => ?_⟩
        obtain ⟨c', hc', hy'⟩ := Set.mem_iUnion₂.mp (hZQ j hj hyZ)
        have hcc : c ≠ c' := fun h => hQavail j hj c' hc' (h ▸ hc)
        exact Set.disjoint_left.mp (hcf_d c c' hcc) hy hy'
      · rw [hPset] at hyP
        rcases hyP with h | h
        · refine ⟨hflatR _ h, fun j hj hyZ => hyW (σ j) (hσN j hj) hyZ.1⟩
        · exact absurd (hDW (σ i) (hσN i hi) (by rw [hπσ i hi]; exact h)) (hyW _ (hσN i hi))
    · rintro ⟨hyR, hyZ⟩
      rw [← hcU] at hyR
      obtain ⟨c, hc, hy⟩ := Set.mem_iUnion₂.mp hyR
      rcases hcover c (Finset.mem_range.mp hc) with h | ⟨i, hi, hci⟩
      · exact Or.inl ⟨c, h, hy⟩
      · refine Or.inr ⟨⟨i, hi, ?_⟩, fun a ha hyW => ?_⟩
        · rw [hPset]; exact Or.inl (Set.mem_iUnion₂.mpr ⟨c, hci, hy⟩)
        · have hWa : (W a).toSet = (D (π a)).toSet ∪ Z (π a) := by
            rw [← hZW (π a) (hπ.mapsTo ha), hσπ a ha]
          rw [hWa] at hyW
          rcases hyW with h | h
          · exact Set.disjoint_left.mp (hDc (π a) (hπ.mapsTo ha) c) h hy
          · exact hyZ (π a) (hπ.mapsTo ha) h
  -- the query bound
  have hqc : (queryCount (tr3 ++ tc4) : ℝ) ≤
      (N.card : ℝ) / ε + (N.card : ℝ) ^ 3 * ((N.card.factorial : ℝ)) ^ 2 := by
    have happ : queryCount (tr3 ++ tc4) = queryCount tr3 + queryCount tc4 := by
      simp [queryCount, List.countP_append]
    have hq0 : queryCount ([] : List (Event ι)) = 0 := rfl
    have hA : queryCount tr3 ≤ N.card * (M - 1) * (N.card + 1) := by
      rw [hq3, hq2]; rw [hq0] at hq1; omega
    have hB : queryCount tc4 ≤ (N.card + 1) * (N.card.choose 2 * N.card.factorial ^ 2) := by
      refine hq6.trans (Nat.mul_le_mul_left _ ?_); omega
    have hch : 2 * N.card.choose 2 = N.card * (N.card - 1) := by
      rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd
    have hB' : 2 * queryCount tc4 ≤ (N.card + 1) * (N.card * (N.card - 1)) * N.card.factorial ^ 2 := by
      calc 2 * queryCount tc4 ≤ 2 * ((N.card + 1) * (N.card.choose 2 * N.card.factorial ^ 2)) := by omega
        _ = (N.card + 1) * (2 * N.card.choose 2) * N.card.factorial ^ 2 := by ring
        _ = _ := by rw [hch]
    rw [happ, Nat.cast_add]
    have hAr : (queryCount tr3 : ℝ) ≤ N.card * ((M : ℝ) - 1) * (N.card + 1) := by
      have : ((N.card * (M - 1) * (N.card + 1) : ℕ) : ℝ) = N.card * ((M : ℝ) - 1) * (N.card + 1) := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
      rw [← this]; exact_mod_cast hA
    have hBr : 2 * (queryCount tc4 : ℝ) ≤ (N.card + 1) * (N.card * (N.card - 1)) * (N.card.factorial : ℝ) ^ 2 := by
      have : (((N.card + 1) * (N.card * (N.card - 1)) * N.card.factorial ^ 2 : ℕ) : ℝ) =
          (N.card + 1) * (N.card * (N.card - 1)) * (N.card.factorial : ℝ) ^ 2 := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
      rw [← this]; exact_mod_cast hB'
    have hfac : (0 : ℝ) ≤ (N.card.factorial : ℝ) ^ 2 := by positivity
    have hBr' : (queryCount tc4 : ℝ) ≤ (N.card : ℝ) ^ 3 * (N.card.factorial : ℝ) ^ 2 := by
      have : (N.card + 1) * (N.card * ((N.card : ℝ) - 1)) ≤ 2 * (N.card : ℝ) ^ 3 := by nlinarith
      nlinarith
    have hAr' : (N.card : ℝ) * ((M : ℝ) - 1) * (N.card + 1) ≤ (N.card : ℝ) / ε := by
      have hM' : (M : ℝ) - 1 < 1 / (3 * (N.card : ℝ) * ε) := by linarith
      have hMm : (0 : ℝ) ≤ (M : ℝ) - 1 := by
        have : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
        linarith
      have h1 : (N.card : ℝ) * (N.card + 1) * (1 / (3 * (N.card : ℝ) * ε)) = (N.card + 1) / (3 * ε) := by
        field_simp
      have h2 : ((N.card : ℝ) + 1) / (3 * ε) ≤ (N.card : ℝ) / ε := by
        rw [div_le_div_iff₀ (by positivity) hε]; nlinarith
      have h3 : (N.card : ℝ) * ((M : ℝ) - 1) * (N.card + 1) ≤
          (N.card : ℝ) * (N.card + 1) * (1 / (3 * (N.card : ℝ) * ε)) := by
        have := mul_le_mul_of_nonneg_left hM'.le (show (0 : ℝ) ≤ (N.card : ℝ) * (N.card + 1) by positivity)
        linarith
      linarith
    linarith
  exact ⟨W, _, s2, tr3 ++ tc4, hexec, hEFW, ⟨σ, Z, hσ, hZR, hZd, hZW, hZv, hres⟩, hqc⟩

end L4Aux

open L4Aux in
theorem solution {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 2 ≤ N.card) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / (6 * (N.card : ℝ) ^ 3))
    (D : ι → Piece) (R : Piece) (hD : ∀ i ∈ N, (D i).WF) (hR : R.WF)
    (hDdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (D i).toSet (D j).toSet)
    (hDR : ∀ i ∈ N, Disjoint (D i).toSet R.toSet)
    (hpos : ∀ i ∈ N, 0 < (V i).value R.toSet)
    (halmost : ∀ i ∈ N, ∀ j ∈ N,
      (V i).value (D j).toSet - ε * (V i).value R.toSet ≤ (V i).value (D i).toSet)
    (s : Rec ι) (hs : s.Valid V N) (hDs : ∀ i ∈ N, s.Aligned (D i)) (hRs : s.Aligned R)
    (o : ChoiceOracle ι) :
    ∃ (W : ι → Piece) (U : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (repair N D R ε) s = some ((W, U), s', tr) ∧
      EnvyFree V N (fun i => (W i).toSet) ∧
      (∃ (σ : ι → ι) (Z : ι → Set ℝ), Set.BijOn σ (N : Set ι) (N : Set ι) ∧
        (∀ j ∈ N, Z j ⊆ R.toSet) ∧
        (∀ j ∈ N, ∀ k ∈ N, j ≠ k → Disjoint (Z j) (Z k)) ∧
        (∀ j ∈ N, (W (σ j)).toSet = (D j).toSet ∪ Z j) ∧
        (∀ i ∈ N, ∀ j ∈ N,
          (V i).value (Z j) ≤ 3 * (N.card : ℝ) ^ 2 * ε * (V i).value R.toSet) ∧
        U.toSet = R.toSet \ ⋃ j ∈ N, Z j) ∧
      (queryCount tr : ℝ) ≤ (N.card : ℝ) / ε + (N.card : ℝ) ^ 3 * ((N.card.factorial : ℝ)) ^ 2 :=
  lemma4_main V N hN ε hε hε' D R hD hR hDdisj hDR hpos halmost s hs hDs hRs o
