-- Prove2me | solution 1 for EnvyFreeCake104.Divide.dominate_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T17:45:12.452294+00:00
-- url     : https://prove2.me/submissions/7cf33686-188d-4671-943d-a3ff125ecb5a

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_lemma_3
import Theorems.Thm_EnvyFreeCake104_Divide_core_invariants
import Theorems.Thm_EnvyFreeCake104_Divide_repair_invariants
import Theorems.Thm_EnvyFreeCake104_Divide_repair_partition

open EnvyFreeCake104.Divide

namespace DIAux

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
/-- A Core call from any transcript: Lemma 3 plus the run invariants. -/
theorem core_run {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 2 ≤ N.card) (c : ι) (hc : c ∈ N) (C : Piece) (hC : C.WF)
    (s : Rec ι) (hs : s.Valid V N) (hCs : s.Aligned C) (o : ChoiceOracle ι)
    (tr₀ : List (Event ι)) :
    ∃ (Y : ι → Piece) (U : Piece) (s' : Rec ι) (tc : List (Event ι)),
      Prog.run V o ((core N c C).run s) tr₀ = some (((Y, U), s'), tr₀ ++ tc) ∧
      IsPartialAlloc N C.toSet (fun i => (Y i).toSet) ∧
      U.toSet = residue N C.toSet (fun i => (Y i).toSet) ∧
      EnvyFree V N (fun i => (Y i).toSet) ∧
      (V c).value (Y c).toSet = (V c).value C.toSet / (N.card : ℝ) ∧
      queryCount tc ≤ N.card ^ 3 * (N.card.factorial) ^ 2 ∧
      s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ (∀ i ∈ N, (Y i).WF ∧ s'.Aligned (Y i)) ∧
      U.WF ∧ s'.Aligned U := by
  obtain ⟨Y, U, s', tc, hex, h1, h2, h3, h4, h5⟩ :=
    EnvyFreeCake104.Divide.lemma_3 V N hN c hc C hC s hs hCs (fun t m ↦ o (tr₀ ++ t) m)
  have hrun := run_from_exec V o _ s tr₀ _ s' tc hex
  obtain ⟨g1, g2, g3, g4, g5⟩ :=
    EnvyFreeCake104.Divide.core_invariants V N hN c hc C hC s hs hCs o tr₀ Y U s' _ hrun
  exact ⟨Y, U, s', tc, hrun, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5⟩

/-- The value of the cake splits into the bundles of a partial allocation and its residue. -/
theorem value_partition {ι : Type} [DecidableEq ι] (v : Valuation) (N : Finset ι) (C : Set ℝ)
    (Y : ι → Set ℝ) (U : Set ℝ) (hY : ∀ i, MeasurableSet (Y i)) (hU : MeasurableSet U)
    (hpa : IsPartialAlloc N C Y) (hres : U = residue N C Y) :
    v.value C = ∑ i ∈ N, v.value (Y i) + v.value U := by
  have hsub : (⋃ i ∈ N, Y i) ⊆ C := Set.iUnion₂_subset hpa.1
  have hC : C = (⋃ i ∈ N, Y i) ∪ U := by
    rw [hres]; unfold residue; exact (Set.union_sdiff_cancel hsub).symm
  have hd : Disjoint (⋃ i ∈ N, Y i) U := by rw [hres]; exact Set.disjoint_sdiff_right
  rw [hC, value_union v hU hd, value_biUnion v Y N (fun i _ => hY i) hpa.2]
theorem permOfLists_getElem {ι : Type} [DecidableEq ι] : ∀ (l l' : List ι) (_ : l.Nodup)
    (hlen : l.length = l'.length) (k : ℕ) (hk : k < l.length),
    permOfLists l l' l[k] = l'[k]'(hlen ▸ hk) := by
  intro l
  induction l with
  | nil => intro l' _ _ k hk; simp at hk
  | cons a l ih =>
    intro l' hnd hlen k hk
    cases l' with
    | nil => simp at hlen
    | cons b l' =>
      rw [List.nodup_cons] at hnd
      cases k with
      | zero => simp [permOfLists]
      | succ k =>
        have hk' : k < l.length := by simpa using hk
        simp only [List.getElem_cons_succ, permOfLists]
        have hne : l[k]'hk' ≠ a := fun h => hnd.1 (h ▸ List.getElem_mem _)
        rw [if_neg hne]
        exact ih l' hnd.2 (by simpa using hlen) k hk'

theorem permOfLists_notMem {ι : Type} [DecidableEq ι] : ∀ (l l' : List ι) (x : ι), x ∉ l →
    permOfLists l l' x = x := by
  intro l
  induction l with
  | nil => intro l' x _; cases l' <;> rfl
  | cons a l ih =>
    intro l' x hx
    cases l' with
    | nil => rfl
    | cons b l' =>
      simp only [List.mem_cons, not_or] at hx
      simp only [permOfLists, if_neg hx.1]
      exact ih l' x hx.2

/-- For a permutation `l'` of `N.toList`, `permOfLists N.toList l'` is a bijection of `N`. -/
theorem permOfLists_bijOn {ι : Type} [DecidableEq ι] (N : Finset ι) (l' : List ι)
    (hl' : l' ∈ N.toList.permutations) :
    Set.BijOn (permOfLists N.toList l') (N : Set ι) (N : Set ι) := by
  rw [List.mem_permutations] at hl'
  have hnd := Finset.nodup_toList N
  have hnd' : l'.Nodup := hl'.nodup_iff.mpr hnd
  have hlen : N.toList.length = l'.length := hl'.length_eq.symm
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hxl : x ∈ N.toList := Finset.mem_toList.mpr hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hxl
    rw [permOfLists_getElem _ _ hnd hlen k hk]
    have := List.getElem_mem (l := l') (by omega : k < l'.length)
    rw [hl'.mem_iff, Finset.mem_toList] at this
    exact this
  · intro x hx y hy hxy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (Finset.mem_toList.mpr hx)
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem (Finset.mem_toList.mpr hy)
    rw [permOfLists_getElem _ _ hnd hlen k hk, permOfLists_getElem _ _ hnd hlen m hm] at hxy
    have := (hnd'.getElem_inj_iff).mp hxy
    simp [this]
  · intro y hy
    have hyl : y ∈ l' := by rw [hl'.mem_iff]; exact Finset.mem_toList.mpr hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hyl
    have hk' : k < N.toList.length := by omega
    exact ⟨N.toList[k], Finset.mem_toList.mp (List.getElem_mem _),
      permOfLists_getElem _ _ hnd hlen k hk'⟩

/-- Weak loop invariant: records valid, residue and bundles well formed and aligned, bundles
pairwise disjoint and disjoint from the residue. -/
def WInv {ι : Type} (V : ι → Valuation) (N : Finset ι) (X : ι → Piece) (R : Piece)
    (t : Rec ι) : Prop :=
  t.Valid V N ∧ R.WF ∧ t.Aligned R ∧ (∀ i ∈ N, (X i).WF ∧ t.Aligned (X i)) ∧
  (∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (X i).toSet (X j).toSet) ∧
  (∀ i ∈ N, Disjoint (X i).toSet R.toSet)

/-- Determinism: a successful Core run is the one given by `core_run`. -/
theorem core_det {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 2 ≤ N.card) (c : ι) (hc : c ∈ N) (C : Piece) (hC : C.WF)
    (s : Rec ι) (hs : s.Valid V N) (hCs : s.Aligned C) (o : ChoiceOracle ι)
    (tr₀ : List (Event ι)) {β : Type} (k : (ι → Piece) × Piece → Proto ι β) (r)
    (h : Prog.run V o ((core N c C >>= k).run s) tr₀ = some r) :
    ∃ (Y : ι → Piece) (U : Piece) (s' : Rec ι) (tc : List (Event ι)),
      Prog.run V o ((k (Y, U)).run s') (tr₀ ++ tc) = some r ∧
      IsPartialAlloc N C.toSet (fun i => (Y i).toSet) ∧
      U.toSet = residue N C.toSet (fun i => (Y i).toSet) ∧
      s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ (∀ i ∈ N, (Y i).WF ∧ s'.Aligned (Y i)) ∧
      U.WF ∧ s'.Aligned U := by
  obtain ⟨Y, U, s', tc, hcore, hpa, hres, -, -, -, h1, h2, h3, h4, h5⟩ :=
    core_run V N hN c hc C hC s hs hCs o tr₀
  rw [run_stbind, hcore] at h
  exact ⟨Y, U, s', tc, h, hpa, hres, h1, h2, h3, h4, h5⟩

theorem shrink_inv {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 2 ≤ N.card) (istar : ι) (hi : istar ∈ N) (α : ℝ) (U : Piece) :
    ∀ (fuel : ℕ) (W : ι → Piece) (R' : Piece) (t : Rec ι) (o : ChoiceOracle ι)
      (tr₀ : List (Event ι)) (W' : ι → Piece) (R'' : Piece) (t' : Rec ι) (tr : List (Event ι)),
      WInv V N W R' t →
      Prog.run V o ((shrink N istar α U fuel W R').run t) tr₀ = some (((W', R''), t'), tr) →
      WInv V N W' R'' t' := by
  intro fuel
  induction fuel with
  | zero =>
    intro W R' t o tr₀ W' R'' t' tr hI h
    rw [shrink.eq_def, run_stbind, run_get'] at h
    dsimp only at h
    split_ifs at h
    · simp [run_fail'] at h
    · rw [run_pure'] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, -⟩ := h
      exact hI
  | succ f ih =>
    intro W R' t o tr₀ W' R'' t' tr hI h
    obtain ⟨hv, hRwf, hRal, hWwa, hWd, hWR⟩ := hI
    rw [shrink.eq_def, run_stbind, run_get'] at h
    dsimp only at h
    split_ifs at h
    · try dsimp only at h
      obtain ⟨F, R2, t1, tc, h', hpa, hres, hv1, hsub1, hFwa, hR2wf, hR2al⟩ :=
        core_det V N hN istar hi R' hRwf t hv hRal o tr₀ _ _ h
      apply ih _ _ t1 o _ W' R'' t' tr _ h'
      have hFR : ∀ i ∈ N, (F i).toSet ⊆ R'.toSet := hpa.1
      have hR2R : R2.toSet ⊆ R'.toSet := by rw [hres]; exact Set.sdiff_subset
      have hWF : ∀ i ∈ N, ∀ j ∈ N, Disjoint (W i).toSet (F j).toSet :=
        fun i hi j hj => Disjoint.mono_right (hFR j hj) (hWR i hi)
      have hFR2 : ∀ i ∈ N, Disjoint (F i).toSet R2.toSet := by
        intro i hi; rw [hres]; unfold residue
        exact Disjoint.mono_left (Set.subset_biUnion_of_mem (u := fun j => (F j).toSet) hi)
          Set.disjoint_sdiff_right
      refine ⟨hv1, hR2wf, hR2al, fun i hi => ⟨wf_append _ _ (hWwa i hi).1 (hFwa i hi).1
        (hWF i hi i hi), aligned_append t1 _ _ (aligned_mono t t1 hsub1 _ (hWwa i hi).2)
        (hFwa i hi).2⟩, ?_, ?_⟩
      · intro i hi j hj hij
        rw [toSet_append, toSet_append]
        exact Disjoint.union_left (Disjoint.union_right (hWd i hi j hj hij) (hWF i hi j hj))
          (Disjoint.union_right (hWF j hj i hi).symm (hpa.2 i hi j hj hij))
      · intro i hi
        rw [toSet_append]
        exact Disjoint.union_left (Disjoint.mono_right hR2R (hWR i hi)) (hFR2 i hi)
    · rw [run_pure'] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, -⟩ := h
      exact ⟨hv, hRwf, hRal, hWwa, hWd, hWR⟩

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

open scoped Classical in
theorem loop_inv {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 3 ≤ N.card) (c : ι) (hc : c ∈ N) :
    ∀ (fuel : ℕ) (X : ι → Piece) (R : Piece) (t : Rec ι) (o : ChoiceOracle ι)
      (tr₀ : List (Event ι)) (X' : ι → Piece) (R' : Piece) (E : Finset ι) (t' : Rec ι)
      (tr : List (Event ι)),
      WInv V N X R t →
      Prog.run V o ((dominateLoop N c fuel X R).run t) tr₀ = some (((X', R', E), t'), tr) →
      t'.Valid V N ∧ R'.WF ∧ t'.Aligned R' := by
  intro fuel
  induction fuel with
  | zero =>
    intro X R t o tr₀ X' R' E t' tr _ h
    rw [dominateLoop] at h; simp [run_fail'] at h
  | succ f ih =>
    intro X R t o tr₀ X' R' E t' tr hI h
    obtain ⟨hv, hRwf, hRal, hXwa, hXd, hXR⟩ := hI
    rw [dominateLoop] at h
    obtain ⟨Y, U, t1, tc, h, hpa, hres, hv1, hsub1, hYwa, hUwf, hUal⟩ :=
      core_det V N (by omega) c hc R hRwf t hv hRal o tr₀ _ _ h
    have hYR : ∀ i ∈ N, (Y i).toSet ⊆ R.toSet := hpa.1
    have hUR : U.toSet ⊆ R.toSet := by rw [hres]; exact Set.sdiff_subset
    have hYU : ∀ i ∈ N, Disjoint (Y i).toSet U.toSet := fun i hi => by
      rw [hres]; unfold residue
      exact Disjoint.mono_left (Set.subset_biUnion_of_mem (u := fun j => (Y j).toSet) hi)
        Set.disjoint_sdiff_right
    have hXY : ∀ i ∈ N, ∀ j ∈ N, Disjoint (X i).toSet (Y j).toSet :=
      fun i hi j hj => Disjoint.mono_right (hYR j hj) (hXR i hi)
    dsimp only at h
    rw [run_stbind, run_get'] at h
    dsimp only at h
    split_ifs at h with hg
    · rw [run_stbind] at h
      rcases hch : Prog.run V o ((chooseP (List.filter (fun E => decide (recDominatedGroup t1 N
          (fun i => X i ++ Y i) U E)) N.powerset.toList) : Proto ι (Finset ι)).run t1) (tr₀ ++ tc) with
        _ | ⟨⟨E', t2⟩, tr2⟩
      · rw [hch] at h; simp at h
      · rw [hch] at h
        obtain ⟨rfl, -⟩ := choose_state V o _ t1 _ E' t2 tr2 hch
        dsimp only at h
        rw [run_pure'] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨⟨-, rfl, -⟩, rfl⟩, -⟩ := h
        exact ⟨hv1, hUwf, hUal⟩
    · rw [run_stbind] at h
      rcases hch : Prog.run V o ((chooseP (line7Options t1 N X R Y U)).run t1) (tr₀ ++ tc) with
        _ | ⟨⟨⟨t'', is, js, l'⟩, t2⟩, tr2⟩
      · rw [hch] at h; simp at h
      · rw [hch] at h
        obtain ⟨ht2, hopt⟩ := choose_state V o _ t1 _ _ t2 tr2 hch
        rw [ht2] at h
        have hl' : l' ∈ N.toList.permutations := by
          unfold line7Options at hopt
          simp only [List.mem_filter, List.pair_mem_product] at hopt
          exact hopt.1.2.2.2
        have hπ := permOfLists_bijOn N l' hl'
        have hπN : ∀ i ∈ N, permOfLists N.toList l' i ∈ N := fun i hi => hπ.mapsTo hi
        dsimp only at h
        rw [run_stbind] at h
        have hDwf : ∀ i ∈ N, (X i ++ Y (permOfLists N.toList l' i)).WF := fun i hi =>
          wf_append _ _ (hXwa i hi).1 (hYwa _ (hπN i hi)).1 (hXY i hi _ (hπN i hi))
        have hDdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (X i ++ Y (permOfLists N.toList l' i)).toSet
            (X j ++ Y (permOfLists N.toList l' j)).toSet := by
          intro i hi j hj hij
          have hπij : permOfLists N.toList l' i ≠ permOfLists N.toList l' j :=
            fun h => hij (hπ.injOn hi hj h)
          rw [toSet_append, toSet_append]
          exact Disjoint.union_left (Disjoint.union_right (hXd i hi j hj hij) (hXY i hi _ (hπN j hj)))
            (Disjoint.union_right (hXY j hj _ (hπN i hi)).symm
              (hpa.2 _ (hπN i hi) _ (hπN j hj) hπij))
        have hDU : ∀ i ∈ N, Disjoint (X i ++ Y (permOfLists N.toList l' i)).toSet U.toSet := by
          intro i hi; rw [toSet_append]
          exact Disjoint.union_left (Disjoint.mono_right hUR (hXR i hi)) (hYU _ (hπN i hi))
        have hDal : ∀ i ∈ N, t1.Aligned (X i ++ Y (permOfLists N.toList l' i)) := fun i hi =>
          aligned_append t1 _ _ (aligned_mono t t1 hsub1 _ (hXwa i hi).2) (hYwa _ (hπN i hi)).2
        rcases hr : Prog.run V o ((repair N (fun i => X i ++ Y (permOfLists N.toList l' i)) U
            (alphaOf N.card t'')).run t1) tr2 with _ | ⟨⟨⟨W, R'0⟩, t3⟩, tr3⟩
        · rw [hr] at h; simp at h
        · rw [hr] at h
          obtain ⟨hv3, -, hWwa, hR'wf, hR'al⟩ := EnvyFreeCake104.Divide.repair_invariants V N _ U _
            hDwf hUwf hDdisj hDU t1 hv1 hDal hUal o tr2 W R'0 t3 tr3 hr
          obtain ⟨hWd, -, hR'eq⟩ := EnvyFreeCake104.Divide.repair_partition V N _ U _
            hDwf hUwf hDdisj hDU t1 hv1 hDal hUal o tr2 W R'0 t3 tr3 hr
          dsimp only at h
          rw [run_stbind] at h
          rcases hs : Prog.run V o ((shrink N is (alphaOf N.card t'') U f W R'0).run t3) tr3 with
            _ | ⟨⟨⟨W', R''⟩, t4⟩, tr4⟩
          · rw [hs] at h; simp at h
          · rw [hs] at h
            dsimp only at h
            have hI3 : WInv V N W R'0 t3 := by
              refine ⟨hv3, hR'wf, hR'al, hWwa, hWd, fun i hi => ?_⟩
              rw [hR'eq]
              exact Disjoint.mono_left (Set.subset_biUnion_of_mem (u := fun j => (W j).toSet) hi)
                Set.disjoint_sdiff_right
            have hI4 := shrink_inv V N (by omega) is ?_ _ U f W R'0 t3 o tr3 W' R'' t4 tr4 hI3 hs
            · exact ih W' R'' t4 o tr4 X' R' E t' tr hI4 h
            · unfold line7Options at hopt
              simp only [List.mem_filter, List.pair_mem_product, Finset.mem_toList] at hopt
              exact hopt.1.2.1

end DIAux

open DIAux in
theorem solution {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 3 ≤ N.card) (C : Piece) (hC : C.WF) (s : Rec ι) (hs : s.Valid V N)
    (hCs : s.Aligned C) (fuel : ℕ) (o : ChoiceOracle ι) (tr₀ : List (Event ι))
    (X : ι → Piece) (R : Piece) (E : Finset ι) (s' : Rec ι) (tr : List (Event ι))
    (hrun : Prog.run V o ((dominate fuel N C).run s) tr₀ = some (((X, R, E), s'), tr)) :
    s'.Valid V N ∧ R.WF ∧ s'.Aligned R := by
  unfold dominate at hrun
  rw [run_stbind] at hrun
  rcases hch : Prog.run V o ((chooseP N.toList : Proto ι ι).run s) tr₀ with _ | ⟨⟨c, t1⟩, tr1⟩
  · rw [hch] at hrun; simp at hrun
  · rw [hch] at hrun
    obtain ⟨ht1, hc⟩ := choose_state V o _ s _ c t1 tr1 hch
    rw [ht1] at hrun
    exact loop_inv V N hN c (Finset.mem_toList.mp hc) fuel _ C s o tr1 X R E s' tr
      ⟨hs, hC, hCs, fun i _ => ⟨wf_nil, fun I hI => by simp at hI⟩, fun i _ j _ _ => by
        simp [toSet_nil], fun i _ => by simp [toSet_nil]⟩ hrun
