-- Prove2me | solution 1 for EnvyFreeCake104.Divide.repair_partition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T18:01:18.826768+00:00
-- url     : https://prove2.me/submissions/defd05d8-04a8-47fd-8b2d-32ca09270f28

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_query_bound__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1
import Theorems.Thm_EnvyFreeCake104_Divide_splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
import Theorems.Thm_EnvyFreeCake104_Divide_split_update_valid__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
import Theorems.Thm_EnvyFreeCake104_Divide_recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
import Theorems.Thm_EnvyFreeCake104_Divide_lemma_6
import Theorems.Thm_EnvyFreeCake104_Divide_permute_invariants
open EnvyFreeCake104.Divide
namespace RPAux

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
section recmono
variable {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)

/-- The record relation: validity is preserved and recorded points only grow. -/
def RM : Rec ι → List (Event ι) → Rec ι → List (Event ι) → Prop :=
  fun s _ s' _ => (s.Valid V N → s'.Valid V N) ∧ s.pts ⊆ s'.pts

theorem rm_refl : ∀ (s : Rec ι) tr, RM V N s tr s tr := fun _ _ => ⟨id, subset_rfl⟩
theorem rm_trans : ∀ (s₁ : Rec ι) t₁ s₂ t₂ s₃ t₃, RM V N s₁ t₁ s₂ t₂ → RM V N s₂ t₂ s₃ t₃ →
    RM V N s₁ t₁ s₃ t₃ := fun _ _ _ _ _ _ h1 h2 => ⟨h2.1 ∘ h1.1, h1.2.trans h2.2⟩

theorem findCell_mem (s : Rec ι) (i : ι) : ∀ (l : List ℝ) (w c w' : ℝ),
    findCell s i l w = some (c, w') → c ∈ l := by
  intro l
  induction l with
  | nil => intro w c w' h; simp [findCell] at h
  | cons x xs ih =>
    intro w c w' h
    simp only [findCell] at h
    split_ifs at h with hx
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih _ c w' h)

theorem rm_choose {β : Type} (l : List β) : Inv V (RM V N) (chooseP l : Proto ι β) := by
  cases l with
  | nil => exact inv_fail V _ (rm_refl V N)
  | cons b bs =>
    intro s o tr₀ y s' tr h
    change Prog.run V o (Prog.bind (Prog.choose bs.length (fun c => Prog.ret ((b :: bs).get c)))
      (fun a => Prog.ret (a, s))) tr₀ = _ at h
    simp only [Prog.bind, Prog.run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, rfl⟩ := h
    exact ⟨id, subset_rfl⟩

theorem rm_prefixCut (i : ι) (P : Piece) (w : ℝ) : Inv V (RM V N) (prefixCut N i P w) := by
  intro s o tr₀ p s' tr h
  simp only [prefixCut, StateT.run_bind, StateT.run_modify, StateT.run_get] at h
  set s1 : Rec ι := { s with prefixCuts := s.prefixCuts + 1 } with hs1
  have hv1 : s.Valid V N → s1.Valid V N := fun hv => hv
  change Prog.run V o (StateT.run (match findInterval s1 i P 0 w with
    | none => if w ≤ 0 then pure (P.length, 0) else failP
    | some (k, w') =>
      if w' ≤ 0 then pure (k, (P.getD k default).a)
      else
        match findCell s1 i
            ((s1.pts.filter (fun c => (P.getD k default).a ≤ c ∧ c < (P.getD k default).b)).sort
              (· ≤ ·)) w' with
        | none => failP
        | some (c, w'') => do
          let y ← cutQ i c w''
          if c < y ∧ y < s1.nextPt c then
            splitCell N c y
          return (k, y)) s1) tr₀ = _ at h
  have hfin : ∀ {m : Proto ι Pos}, Inv V (RM V N) m →
      Prog.run V o (m.run s1) tr₀ = some ((p, s'), tr) → RM V N s tr₀ s' tr := by
    intro m hm hh
    have := hm s1 o tr₀ p s' tr hh
    exact ⟨this.1 ∘ hv1, this.2⟩
  split at h
  · split_ifs at h
    · exact hfin (inv_pure V _ (rm_refl V N) _) h
    · exact hfin (inv_fail V _ (rm_refl V N)) h
  · rename_i k w' _
    split_ifs at h
    · exact hfin (inv_pure V _ (rm_refl V N) _) h
    · split at h
      · exact hfin (inv_fail V _ (rm_refl V N)) h
      · rename_i c w'' hcell
        have hc : c ∈ s1.pts := by
          have := findCell_mem s1 i _ w' c w'' hcell
          rw [Finset.mem_sort] at this
          exact (Finset.mem_filter.mp this).1
        rw [run_stbind] at h
        change (match some ((cutAnswer V i c w'', s1), tr₀ ++ [Event.cut i c w'' (cutAnswer V i c w'')]) with
          | none => none
          | some ((x, t'), tr') => _) = _ at h
        dsimp only at h
        split_ifs at h with hcy
        · rw [run_stbind] at h
          obtain ⟨trs, hsc⟩ := splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2 V N s1
            c (cutAnswer V i c w'') o (tr₀ ++ [Event.cut i c w'' (cutAnswer V i c w'')])
          rw [hsc] at h
          dsimp only at h
          rw [run_pure'] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨-, rfl⟩, -⟩ := h
          refine ⟨fun hv => split_update_valid__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2 V N s1 (hv1 hv) c _
            hc hcy.1 hcy.2, ?_⟩
          intro x hx; exact Finset.mem_insert_of_mem hx
        · rw [run_pure'] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨-, rfl⟩, -⟩ := h
          exact ⟨hv1, subset_rfl⟩

theorem rm_trim (Y : ι → Piece) : ∀ (earlier : List ι) (piece removed : Piece),
    Inv V (RM V N) (trimAgainst N Y earlier piece removed) := by
  intro earlier
  induction earlier with
  | nil => intro piece removed; exact inv_pure V _ (rm_refl V N) _
  | cons a rest ih =>
    intro piece removed
    simp only [trimAgainst]
    refine inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N)) (fun st => ?_)
    apply inv_ite V _ (rm_refl V N)
    · exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_prefixCut V N _ _ _) (fun p => ih _ _)
    · exact ih _ _

theorem rm_candLoop (P : ι → Piece) : ∀ (pairs : List (ι × ι)) (earlier : List ι)
    (Y : ι → Piece) (R : Piece), Inv V (RM V N) (candidateLoop N P pairs earlier Y R) := by
  intro pairs
  induction pairs with
  | nil => intro earlier Y R; exact inv_pure V _ (rm_refl V N) _
  | cons q rest ih =>
    intro earlier Y R
    obtain ⟨i, j⟩ := q
    simp only [candidateLoop]
    exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_trim V N Y _ _ _)
      (fun x => by obtain ⟨pc, rm⟩ := x; exact ih _ _ _)

theorem rm_permute (P : ι → Piece) : Inv V (RM V N) (permute N P) := by
  have : ∀ (k : ℕ) (gs : List (List ι × List ι)), Inv V (RM V N) (permuteLoop N P k gs) := by
    intro k
    induction k with
    | zero => intro gs; exact inv_fail V _ (rm_refl V N)
    | succ k ih =>
      intro gs
      simp only [permuteLoop]
      refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_choose V N gs) (fun g => ?_)
      refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_candLoop V N P _ _ _ _) (fun x => ?_)
      obtain ⟨Y, R⟩ := x
      refine inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N)) (fun st => ?_)
      split_ifs
      · exact inv_pure V _ (rm_refl V N) _
      · exact ih _
  exact this _ _

theorem rm_equalCuts (c : ι) (w : ℝ) : ∀ (m : ℕ) (rest : Piece),
    Inv V (RM V N) (equalCuts N c w m rest) := by
  intro m
  induction m with
  | zero => intro rest; exact inv_pure V _ (rm_refl V N) _
  | succ m ih =>
    intro rest
    simp only [equalCuts]
    exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_prefixCut V N _ _ _)
      (fun p => inv_bind V _ (rm_refl V N) (rm_trans V N) (ih _) (fun _ => inv_pure V _ (rm_refl V N) _))

theorem rm_core (c : ι) (C : Piece) : Inv V (RM V N) (core N c C) := by
  unfold core
  refine inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N)) (fun st => ?_)
  exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_equalCuts V N _ _ _ _)
    (fun ps => rm_permute V N _)

theorem rm_marksOf (R : Piece) (i : ι) (v : ℝ) (M : ℕ) : ∀ ts : List ℕ,
    Inv V (RM V N) (marksOf N R i v M ts) := by
  intro ts
  induction ts with
  | nil => exact inv_pure V _ (rm_refl V N) _
  | cons t ts ih =>
    simp only [marksOf]
    exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_prefixCut V N _ _ _)
      (fun p => inv_bind V _ (rm_refl V N) (rm_trans V N) ih (fun _ => inv_pure V _ (rm_refl V N) _))

theorem rm_allMarks (R : Piece) (v : ι → ℝ) (M : ℕ) : ∀ l : List ι,
    Inv V (RM V N) (allMarks N R v M l) := by
  intro l
  induction l with
  | nil => exact inv_pure V _ (rm_refl V N) _
  | cons i l ih =>
    simp only [allMarks]
    exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_marksOf V N _ _ _ _ _)
      (fun p => inv_bind V _ (rm_refl V N) (rm_trans V N) ih (fun _ => inv_pure V _ (rm_refl V N) _))

theorem rm_rrPick (cells : List Piece) (avail : List ℕ) (i : ι) :
    Inv V (RM V N) (rrPick cells avail i) := by
  unfold rrPick
  exact inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N))
    (fun st => rm_choose V N _)

theorem rm_rrRound (cells : List Piece) : ∀ (order : List ι) (avail : List ℕ) (Q : ι → List ℕ),
    Inv V (RM V N) (rrRound cells order avail Q) := by
  intro order
  induction order with
  | nil => intro avail Q; exact inv_pure V _ (rm_refl V N) _
  | cons i is ih =>
    intro avail Q
    simp only [rrRound]
    exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_rrPick V N _ _ _) (fun c => ih _ _)

theorem rm_roundRobin (cells : List Piece) (order : List ι) : ∀ (r : ℕ) (avail : List ℕ)
    (Q : ι → List ℕ), Inv V (RM V N) (roundRobin cells order r avail Q) := by
  intro r
  induction r with
  | zero => intro avail Q; exact inv_pure V _ (rm_refl V N) _
  | succ r ih =>
    intro avail Q
    simp only [roundRobin]
    exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_rrRound V N _ _ _ _)
      (fun x => by obtain ⟨Q', a'⟩ := x; exact ih _ _)

theorem rm_repair (D : ι → Piece) (R : Piece) (ε : ℝ) : Inv V (RM V N) (repair N D R ε) := by
  unfold repair
  refine inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N)) (fun st => ?_)
  refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_allMarks V N _ _ _ _) (fun marks => ?_)
  refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_choose V N _) (fun order => ?_)
  refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_roundRobin V N _ _ _ _ _) (fun x => ?_)
  obtain ⟨Q, avail⟩ := x
  refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_permute V N _) (fun x => ?_)
  obtain ⟨W, U⟩ := x
  exact inv_pure V _ (rm_refl V N) _

theorem rm_shrink (istar : ι) (α : ℝ) (U : Piece) : ∀ (fuel : ℕ) (W : ι → Piece) (R' : Piece),
    Inv V (RM V N) (shrink N istar α U fuel W R') := by
  intro fuel
  induction fuel with
  | zero =>
    intro W R'
    rw [shrink.eq_def]
    refine inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N)) (fun st => ?_)
    split_ifs
    · exact inv_fail V _ (rm_refl V N)
    · exact inv_pure V _ (rm_refl V N) _
  | succ f ih =>
    intro W R'
    rw [shrink.eq_def]
    refine inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N)) (fun st => ?_)
    split_ifs
    · dsimp only
      exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_core V N _ _)
        (fun x => by obtain ⟨F, R''⟩ := x; exact ih _ _)
    · exact inv_pure V _ (rm_refl V N) _

theorem rm_dominateLoop (c : ι) : ∀ (fuel : ℕ) (X : ι → Piece) (R : Piece),
    Inv V (RM V N) (dominateLoop N c fuel X R) := by
  intro fuel
  induction fuel with
  | zero => intro X R; rw [dominateLoop]; exact inv_fail V _ (rm_refl V N)
  | succ f ih =>
    intro X R
    rw [dominateLoop]
    refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_core V N _ _) (fun x => ?_)
    obtain ⟨Y, U⟩ := x
    try dsimp only
    refine inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N)) (fun st => ?_)
    try dsimp only
    split_ifs
    · exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_choose V N _)
        (fun _ => inv_pure V _ (rm_refl V N) _)
    · refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_choose V N _) (fun x => ?_)
      obtain ⟨t, istar, jstar, l'⟩ := x
      try dsimp only
      refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_repair V N _ _ _) (fun x => ?_)
      obtain ⟨W, R'⟩ := x
      try dsimp only
      refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_shrink V N _ _ _ _ _ _) (fun x => ?_)
      obtain ⟨W', R''⟩ := x
      exact ih _ _

theorem rm_dominate (fuel : ℕ) (C : Piece) : Inv V (RM V N) (dominate fuel N C) := by
  unfold dominate
  exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_choose V N _)
    (fun c => rm_dominateLoop V N c _ _ _)

end recmono
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
open scoped Classical in
theorem permute_empty {ι : Type} [DecidableEq ι] (V : ι → Valuation) (P : ι → Piece)
    (t : Rec ι) (o : ChoiceOracle ι) (tr₀ : List (Event ι)) (Y : ι → Piece) (U : Piece)
    (t' : Rec ι) (tr : List (Event ι))
    (h : Prog.run V o ((permute (∅ : Finset ι) P).run t) tr₀ = some (((Y, U), t'), tr)) :
    U = [] := by
  have hg : guesses (∅ : Finset ι) = [([], [])] := by simp [guesses, List.product]
  unfold permute at h
  rw [hg] at h
  simp only [List.length_singleton, permuteLoop] at h
  rw [run_stbind, run_choose_cons] at h
  dsimp only at h
  rw [run_stbind] at h
  have hc : candidate (∅ : Finset ι) P ([] : List ι) [] = pure ((fun _ => []), []) := by
    simp [candidate, candidateLoop]
  have hget : ∀ f : Fin 1, ([(([] : List ι), ([] : List ι))]).get f = ([], []) := by
    intro f; fin_cases f; rfl
  rw [hget, hc, run_pure'] at h
  dsimp only at h
  rw [run_stbind, run_get'] at h
  dsimp only at h
  rw [if_pos (by intro i hi; simp at hi), run_pure'] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact h.1.1.2.symm

open scoped Classical in
theorem repair_struct {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (D : ι → Piece) (R : Piece) (ε : ℝ) (hD : ∀ i ∈ N, (D i).WF) (hR : R.WF)
    (hDdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (D i).toSet (D j).toSet)
    (hDR : ∀ i ∈ N, Disjoint (D i).toSet R.toSet)
    (s : Rec ι) (hs : s.Valid V N) (hDs : ∀ i ∈ N, s.Aligned (D i)) (hRs : s.Aligned R)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι))
    (W : ι → Piece) (U : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : Prog.run V o ((repair N D R ε).run s) tr₀ = some (((W, U), s'), tr)) :
    s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ (∀ i ∈ N, (W i).WF ∧ s'.Aligned (W i)) ∧
      U.WF ∧ s'.Aligned U ∧
      (∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (W i).toSet (W j).toSet) ∧
      (∀ i ∈ N, (W i).toSet ⊆ R.toSet ∪ ⋃ j ∈ N, (D j).toSet) ∧
      U.toSet = (R.toSet ∪ ⋃ j ∈ N, (D j).toSet) \ ⋃ i ∈ N, (W i).toSet := by
  have hmeas : ∀ P : Piece, MeasurableSet P.toSet := piece_measurable
  unfold repair at hrun
  rw [run_stbind, run_get'] at hrun
  dsimp only at hrun
  rw [run_stbind] at hrun
  rcases hmk : Prog.run V o ((allMarks N R (fun i => s.pieceVal i R) ⌈1 / (3 * (N.card : ℝ) * ε)⌉₊
      N.toList).run s) tr₀ with _ | ⟨⟨ms, s1⟩, tr1⟩
  · rw [hmk] at hrun; simp at hrun
  rw [hmk] at hrun
  dsimp only at hrun
  have hRM1 := rm_allMarks V N R _ _ N.toList s o tr₀ ms s1 tr1 hmk
  have hs1 : s1.Valid V N := hRM1.1 hs
  have hsub1 : s.pts ⊆ s1.pts := hRM1.2
  have hRs1 : s1.Aligned R := aligned_mono s s1 hsub1 _ hRs
  have hmarks : R ≠ [] → ∀ p ∈ ms, R.ValidPos p ∧ s1.Aligned (prefixList R p) := by
    intro hne
    obtain ⟨ms', s1', tr1', hmk', -, -, -, hps, -⟩ := allMarks_ok V N R hR hne (fun i => s.pieceVal i R)
      ⌈1 / (3 * (N.card : ℝ) * ε)⌉₊ (fun i hi => recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
        V N s hs i hi R hR hRs) N.toList (fun i hi => Finset.mem_toList.mp hi) s hs hRs o tr₀
    rw [hmk] at hmk'
    simp only [Option.some.injEq, Prod.mk.injEq] at hmk'
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hmk'
    exact hps
  set cells := cellsOf R ms with hcells
  obtain ⟨hcwa, hcd, hcU⟩ := cells_facts R hR s1 hRs1 ms hmarks
  have hcR : ∀ k, (cells.getD k []).toSet ⊆ R.toSet := by
    intro k
    by_cases hk : k < cells.length
    · rw [← hcU]; exact Set.subset_biUnion_of_mem (u := fun k => (cells.getD k []).toSet)
        (Finset.mem_range.mpr hk)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      simp [toSet_nil]
  -- order and round robin
  rw [run_stbind] at hrun
  rcases hord : Prog.run V o ((chooseP N.toList.permutations : Proto ι (List ι)).run s1) tr1 with
    _ | ⟨⟨order, s2⟩, tr2⟩
  · rw [hord] at hrun; simp at hrun
  rw [hord] at hrun
  obtain ⟨hs2, hordp⟩ := choose_state V o _ s1 _ order s2 tr2 hord
  rw [hs2] at hrun
  dsimp only at hrun
  rw [List.mem_permutations] at hordp
  have hordnd : order.Nodup := hordp.nodup_iff.mpr (Finset.nodup_toList N)
  have hordN : ∀ i, i ∈ order ↔ i ∈ N := fun i => by rw [hordp.mem_iff, Finset.mem_toList]
  rw [run_stbind] at hrun
  rcases hrr : Prog.run V o ((roundRobin cells order (N.card - 1) (List.range cells.length)
      (fun _ => [])).run s1) tr2 with _ | ⟨⟨⟨Q, avail⟩, s3⟩, tr3⟩
  · rw [hrr] at hrun; simp at hrun
  rw [hrr] at hrun
  obtain ⟨hs3, hperm, hQout⟩ := rr_perm_rounds V cells order hordnd cells.length (N.card - 1)
    (List.range cells.length) (fun _ => []) s1 o tr2 Q avail s3 tr3 (by simp) hrr
  rw [hs3] at hrun
  dsimp only at hrun
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
    have := hpw.forall ((hordN i).mpr hi) ((hordN j).mpr hj) hij
    exact this hci hcj
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
  have hlt : ∀ c, (c ∈ avail ∨ ∃ i ∈ N, c ∈ Q i) → c < cells.length := by
    intro c hc
    have : c ∈ (order.map Q).flatten ++ avail := by
      rcases hc with h | ⟨i, hi, h⟩
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ (List.mem_flatten.mpr ⟨Q i, List.mem_map.mpr ⟨i, (hordN i).mpr hi, rfl⟩, h⟩)
    exact List.mem_range.mp (hperm.mem_iff.mp this)
  let cf : ℕ → Piece := fun c => cells.getD c []
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
  -- Permute
  rw [run_stbind] at hrun
  rcases hpm : Prog.run V o ((permute N P).run s1) tr3 with _ | ⟨⟨⟨W0, U0⟩, s4⟩, tr4⟩
  · rw [hpm] at hrun; simp at hrun
  rw [hpm] at hrun
  dsimp only at hrun
  rw [run_pure'] at hrun
  simp only [Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, -⟩ := hrun
  obtain ⟨hv4, hsub4, hWwa, hU0wf, hU0al⟩ := EnvyFreeCake104.Divide.permute_invariants V N P hPwf
    hPdisj s1 hs1 hPal o tr3 W0 U0 s4 tr4 hpm
  -- Permute's residue and bundles
  have hperm6 : U0.toSet = (⋃ i ∈ N, (P i).toSet) \ ⋃ i ∈ N, (W0 i).toSet ∧
      (∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (W0 i).toSet (W0 j).toSet) ∧
      (∀ i ∈ N, (W0 i).toSet ⊆ ⋃ j ∈ N, (P j).toSet) := by
    by_cases hNe : N = ∅
    · subst hNe
      have := permute_empty V P s1 o tr3 W0 U0 s4 tr4 hpm
      subst this
      simp [toSet_nil]
    · have hNne : N.Nonempty := Finset.nonempty_iff_ne_empty.mpr hNe
      obtain ⟨Y6, U6, s6, tr6, hex6, -, hres6, ⟨π, hπ, hsuf, -, -⟩, -⟩ :=
        EnvyFreeCake104.Divide.lemma_6 V N hNne P hPwf hPdisj s1 hs1 hPal (fun t m ↦ o (tr3 ++ t) m)
      have hr6 := run_from_exec V o _ s1 tr3 _ s6 tr6 hex6
      rw [hpm] at hr6
      simp only [Option.some.injEq, Prod.mk.injEq] at hr6
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, -⟩ := hr6
      have hsubP : ∀ i ∈ N, (W0 i).toSet ⊆ (P (π i)).toSet :=
        fun i hi => suffix_sub_piece _ _ (hsuf i hi)
      refine ⟨hres6, fun i hi j hj hij => ?_, fun i hi => (hsubP i hi).trans
        (Set.subset_biUnion_of_mem (u := fun j => (P j).toSet) (hπ.mapsTo hi))⟩
      exact Disjoint.mono (hsubP i hi) (hsubP j hj)
        (hPdisj _ (hπ.mapsTo hi) _ (hπ.mapsTo hj) (fun h => hij (hπ.injOn hi hj h)))
  obtain ⟨hU0set, hWd, hWP⟩ := hperm6
  -- assemble
  have hPU : (⋃ i ∈ N, (P i).toSet) ∪ (⋃ c ∈ avail, (cf c).toSet) = R.toSet ∪ ⋃ j ∈ N, (D j).toSet := by
    apply Set.Subset.antisymm
    · refine Set.union_subset (Set.iUnion₂_subset fun i hi => ?_) ((hflatR _).trans Set.subset_union_left)
      rw [hPset]
      exact Set.union_subset ((hflatR _).trans Set.subset_union_left)
        ((Set.subset_biUnion_of_mem (u := fun j => (D j).toSet) hi).trans Set.subset_union_right)
    · refine Set.union_subset ?_ (Set.iUnion₂_subset fun j hj => ?_)
      · rw [← hcU]
        refine Set.iUnion₂_subset fun c hc => ?_
        rcases hcover c (Finset.mem_range.mp hc) with h | ⟨i, hi, h⟩
        · exact Set.subset_union_right.trans' (Set.subset_biUnion_of_mem (u := fun c => (cf c).toSet) h)
        · refine Set.subset_union_left.trans' ((Set.subset_biUnion_of_mem (u := fun j => (P j).toSet) hi).trans' ?_)
          rw [hPset]
          exact Set.subset_union_left.trans' (Set.subset_biUnion_of_mem (u := fun c => (cf c).toSet) h)
      · refine Set.subset_union_left.trans' ((Set.subset_biUnion_of_mem (u := fun j => (P j).toSet) hj).trans' ?_)
        rw [hPset]; exact Set.subset_union_right
  have hAP : Disjoint (⋃ c ∈ avail, (cf c).toSet) (⋃ i ∈ N, (P i).toSet) := by
    rw [Set.disjoint_iUnion₂_left]; intro c hc
    rw [Set.disjoint_iUnion₂_right]; intro i hi
    rw [hPset]
    refine Disjoint.union_right ?_ (Disjoint.mono_left (hcR c) (hDR i hi).symm)
    rw [Set.disjoint_iUnion₂_right]; intro c' hc'
    exact hcf_d c c' (fun h => hQavail i hi c' hc' (h ▸ hc))
  have hU0P : U0.toSet ⊆ ⋃ i ∈ N, (P i).toSet := by rw [hU0set]; exact Set.sdiff_subset
  refine ⟨hv4, hsub1.trans hsub4, hWwa, ?_, ?_, hWd, ?_, ?_⟩
  · refine wf_append _ _ (flat_wf cf hcf_wf hcf_d _ hndA) hU0wf ?_
    rw [toSet_flatten_map]; exact Disjoint.mono_right hU0P hAP
  · exact aligned_append s4 _ _ (flat_aligned s4 cf (fun c => aligned_mono s1 s4 hsub4 _ (hcf_al c)) _) hU0al
  · intro i hi; rw [← hPU]; exact (hWP i hi).trans Set.subset_union_left
  · rw [toSet_append, toSet_flatten_map, hU0set, ← hPU]
    have hWdisjA : Disjoint (⋃ c ∈ avail, (cf c).toSet) (⋃ i ∈ N, (W0 i).toSet) :=
      Disjoint.mono_right (Set.iUnion₂_subset fun i hi => hWP i hi) hAP
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact ⟨Or.inr h, fun h' => Set.disjoint_left.mp hWdisjA h h'⟩
      · exact ⟨Or.inl h1, h2⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact Or.inl h1

end RPAux

open RPAux in
theorem solution {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (D : ι → Piece) (R : Piece) (ε : ℝ) (hD : ∀ i ∈ N, (D i).WF) (hR : R.WF)
    (hDdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (D i).toSet (D j).toSet)
    (hDR : ∀ i ∈ N, Disjoint (D i).toSet R.toSet)
    (s : Rec ι) (hs : s.Valid V N) (hDs : ∀ i ∈ N, s.Aligned (D i)) (hRs : s.Aligned R)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι))
    (W : ι → Piece) (U : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : Prog.run V o ((repair N D R ε).run s) tr₀ = some (((W, U), s'), tr)) :
    (∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (W i).toSet (W j).toSet) ∧
    (∀ i ∈ N, (W i).toSet ⊆ R.toSet ∪ ⋃ j ∈ N, (D j).toSet) ∧
    U.toSet = (R.toSet ∪ ⋃ j ∈ N, (D j).toSet) \ ⋃ i ∈ N, (W i).toSet := by
  obtain ⟨-, -, -, -, -, h6, h7, h8⟩ :=
    repair_struct V N D R ε hD hR hDdisj hDR s hs hDs hRs o tr₀ W U s' tr hrun
  exact ⟨h6, h7, h8⟩
