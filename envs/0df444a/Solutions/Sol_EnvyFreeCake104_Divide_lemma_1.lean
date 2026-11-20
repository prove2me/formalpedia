-- Prove2me | solution 1 for EnvyFreeCake104.Divide.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T17:42:55.232185+00:00
-- url     : https://prove2.me/submissions/2c09eaf3-0398-4455-ad38-add23ea2bc43

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_lemma_3
import Theorems.Thm_EnvyFreeCake104_Divide_lemma_4
import Theorems.Thm_EnvyFreeCake104_Divide_lemma_5
import Theorems.Thm_EnvyFreeCake104_Divide_core_invariants
import Theorems.Thm_EnvyFreeCake104_Divide_repair_invariants
import Theorems.Thm_EnvyFreeCake104_Divide_repair_partition
import Theorems.Thm_EnvyFreeCake104_Divide_shrink_progress
import Theorems.Thm_EnvyFreeCake104_Divide_recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1

open EnvyFreeCake104.Divide

namespace L1Aux

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

theorem permOfLists_map {ι : Type} [DecidableEq ι] (N : Finset ι) (π : ι → ι) :
    ∀ x ∈ N, permOfLists N.toList (N.toList.map π) x = π x := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (Finset.mem_toList.mpr hx)
  rw [permOfLists_getElem _ _ (Finset.nodup_toList N) (by simp) k hk]
  simp

theorem map_mem_permutations {ι : Type} [DecidableEq ι] (N : Finset ι) (π : ι → ι)
    (hπ : Set.BijOn π (N : Set ι) (N : Set ι)) : N.toList.map π ∈ N.toList.permutations := by
  rw [List.mem_permutations]
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact (List.nodup_map_iff_inj_on (Finset.nodup_toList N)).mpr
      (fun x hx y hy h => hπ.injOn (Finset.mem_toList.mp hx) (Finset.mem_toList.mp hy) h)
  · exact Finset.nodup_toList N
  · ext y
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_toList]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hπ.mapsTo hx
    · intro hy; obtain ⟨x, hx, rfl⟩ := hπ.surjOn hy; exact ⟨x, hx, rfl⟩

/-- The loop invariant of Dominate. -/
def DInv {ι : Type} (V : ι → Valuation) (N : Finset ι) (C : Piece) (X : ι → Piece) (R : Piece)
    (t : Rec ι) : Prop :=
  t.Valid V N ∧ R.WF ∧ t.Aligned R ∧ (∀ i ∈ N, (X i).WF ∧ t.Aligned (X i)) ∧
  (∀ i ∈ N, (X i).toSet ⊆ C.toSet) ∧
  (∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (X i).toSet (X j).toSet) ∧
  R.toSet = C.toSet \ (⋃ i ∈ N, (X i).toSet) ∧ EnvyFree V N (fun i => (X i).toSet)

open scoped Classical in
/-- The domination count `Σ_i |Dom_i(X, R)|`. -/
noncomputable def Phi {ι : Type} (V : ι → Valuation) (N : Finset ι) (X : ι → Piece) (R : Piece) :
    ℕ :=
  ∑ i ∈ N, (N.filter (fun j => (V i).value R.toSet ≤
    (V i).value (X i).toSet - (V i).value (X j).toSet)).card

theorem Phi_le {ι : Type} (V : ι → Valuation) (N : Finset ι) (X : ι → Piece) (R : Piece) :
    Phi V N X R ≤ N.card * N.card := by
  classical
  unfold Phi
  calc _ ≤ ∑ i ∈ N, N.card := Finset.sum_le_sum (fun i _ => Finset.card_filter_le _ _)
    _ = N.card * N.card := by rw [Finset.sum_const, smul_eq_mul]
theorem one_sub_pow_le_half (n : ℕ) (hn : 2 ≤ n) : (1 - 1 / (n : ℝ)) ^ n ≤ 1 / 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h0 : 0 ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hnpos]; exact_mod_cast (show 1 ≤ n by omega)
  have h1 : 1 - 1 / (n : ℝ) ≤ Real.exp (-(1 / n)) := by
    have := Real.add_one_le_exp (-(1 / (n : ℝ))); linarith
  calc (1 - 1 / (n : ℝ)) ^ n ≤ Real.exp (-(1 / n)) ^ n := pow_le_pow_left₀ h0 h1 n
    _ = Real.exp (-1) := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp
    _ ≤ 1 / 2 := by
        rw [Real.exp_neg, one_div]
        apply inv_anti₀ (by norm_num)
        have := Real.add_one_le_exp 1; linarith

theorem four_sq_le_pow (n : ℕ) (hn : 3 ≤ n) : 4 * n ^ 2 ≤ 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    calc 4 * (m + 1) ^ 2 ≤ 4 * (4 * m ^ 2) := by nlinarith
      _ ≤ 4 * 4 ^ m := by omega
      _ = 4 ^ (m + 1) := by ring

/-- Enough Core calls: `(1 - 1/n)^(2n²(n+1)) ≤ (4n²)^{-t}` for `t ≤ n + 1`. -/
theorem shrink_calls (n t : ℕ) (hn : 3 ≤ n) (ht : t ≤ n + 1) :
    (1 - 1 / (n : ℝ)) ^ (2 * n ^ 2 * (n + 1)) ≤ alphaOf n t := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h0 : 0 ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hnpos]; exact_mod_cast (show 1 ≤ n by omega)
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : (1 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
  calc (1 - 1 / (n : ℝ)) ^ (2 * n ^ 2 * (n + 1))
      = ((1 - 1 / (n : ℝ)) ^ n) ^ (2 * n * (n + 1)) := by rw [← pow_mul]; ring_nf
    _ ≤ (1 / 2 : ℝ) ^ (2 * n * (n + 1)) :=
        pow_le_pow_left₀ (pow_nonneg h0 _) (one_sub_pow_le_half n (by omega)) _
    _ = ((4 : ℝ) ^ (n * (n + 1)))⁻¹ := by
        rw [one_div, inv_pow, show 2 * n * (n + 1) = 2 * (n * (n + 1)) by ring, pow_mul]
        norm_num
    _ ≤ ((4 * (n : ℝ) ^ 2) ^ (n + 1))⁻¹ := by
        apply inv_anti₀ (by positivity)
        rw [pow_mul]
        apply pow_le_pow_left₀ (by positivity)
        exact_mod_cast four_sq_le_pow n hn
    _ ≤ alphaOf n t := by
        unfold alphaOf
        apply inv_anti₀ (by positivity)
        exact pow_le_pow_right₀ hq ht

theorem alpha_lower (n t : ℕ) (hn : 1 ≤ n) (ht : t ≤ n + 1) :
    ((4 * (n : ℝ) ^ 2) ^ (n + 1))⁻¹ ≤ alphaOf n t := by
  have hq : (1 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  unfold alphaOf
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hq ht)

theorem pow_le_exp_factorial (n : ℕ) : (n : ℝ) ^ n ≤ Real.exp n * n.factorial := by
  have := Real.pow_div_factorial_le_exp (n : ℝ) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rwa [div_le_iff₀ hf] at this

/-- The query bound of Lemma 1. -/
theorem total_bound (n : ℕ) (hn : 3 ≤ n) :
    (n * n + 1) * (n * (4 * n ^ 2) ^ (n + 1) +
      (2 * n ^ 2 * (n + 1) + 2) * (n ^ 3 * (n.factorial) ^ 2)) ≤
      32 ^ n * n ^ 7 * (n.factorial) ^ 2 := by
  -- second part, in ℕ
  have h2 : 2 * ((n * n + 1) * ((2 * n ^ 2 * (n + 1) + 2) * (n ^ 3 * (n.factorial) ^ 2))) ≤
      32 ^ n * n ^ 7 * (n.factorial) ^ 2 := by
    have hA : n * n + 1 ≤ 2 * n ^ 2 := by nlinarith
    have hB : 2 * n ^ 2 * (n + 1) + 2 ≤ 4 * n ^ 3 := by nlinarith
    have hC : 16 * n ≤ 32 ^ n := by
      have : n < 2 ^ n := Nat.lt_two_pow_self
      calc 16 * n ≤ 16 * 2 ^ n := by omega
        _ ≤ 16 ^ n * 2 ^ n := Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) 16)
        _ = 32 ^ n := by rw [← mul_pow]; norm_num
    calc 2 * ((n * n + 1) * ((2 * n ^ 2 * (n + 1) + 2) * (n ^ 3 * (n.factorial) ^ 2)))
        ≤ 2 * ((2 * n ^ 2) * ((4 * n ^ 3) * (n ^ 3 * (n.factorial) ^ 2))) := by gcongr
      _ = (16 * n) * (n ^ 7 * (n.factorial) ^ 2) := by ring
      _ ≤ 32 ^ n * (n ^ 7 * (n.factorial) ^ 2) := Nat.mul_le_mul_right _ hC
      _ = 32 ^ n * n ^ 7 * (n.factorial) ^ 2 := by ring
  -- first part, in ℝ
  have h1 : 2 * ((n * n + 1) * (n * (4 * n ^ 2) ^ (n + 1))) ≤ 32 ^ n * n ^ 7 * (n.factorial) ^ 2 := by
    have hR : (2 * ((n * n + 1) * (n * (4 * (n : ℝ) ^ 2) ^ (n + 1)))) ≤
        (32 : ℝ) ^ n * (n : ℝ) ^ 7 * ((n.factorial : ℝ)) ^ 2 := by
      have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
      have hf := pow_le_exp_factorial n
      have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have hepos : 0 < Real.exp 1 := Real.exp_pos 1
      have hexp : Real.exp (n : ℝ) = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul]; ring_nf
      have hfac : (0 : ℝ) ≤ n.factorial := by positivity
      -- (4 n²)^{n+1} ≤ 4 n² · 4^n · e^{2n} (n!)²
      have hpow : (4 * (n : ℝ) ^ 2) ^ (n + 1) ≤
          4 * (n : ℝ) ^ 2 * ((4 * Real.exp 1 ^ 2) ^ n * (n.factorial : ℝ) ^ 2) := by
        have : ((n : ℝ) ^ n) ^ 2 ≤ (Real.exp 1 ^ n * n.factorial) ^ 2 := by
          rw [← hexp]; exact pow_le_pow_left₀ (by positivity) hf 2
        calc (4 * (n : ℝ) ^ 2) ^ (n + 1) = 4 * (n : ℝ) ^ 2 * (4 ^ n * ((n : ℝ) ^ n) ^ 2) := by
              ring
          _ ≤ 4 * (n : ℝ) ^ 2 * (4 ^ n * (Real.exp 1 ^ n * n.factorial) ^ 2) := by gcongr
          _ = 4 * (n : ℝ) ^ 2 * ((4 * Real.exp 1 ^ 2) ^ n * (n.factorial : ℝ) ^ 2) := by ring
      have h4e : (4 * Real.exp 1 ^ 2) ^ n ≤ (32 : ℝ) ^ n := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith
      have hn2 : (9 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have hpoly : 8 * ((n : ℝ) * n + 1) ≤ (n : ℝ) ^ 4 := by
        nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 9)]
      calc 2 * (((n : ℝ) * n + 1) * (n * (4 * (n : ℝ) ^ 2) ^ (n + 1)))
          ≤ 2 * (((n : ℝ) * n + 1) * (n * (4 * (n : ℝ) ^ 2 *
              ((4 * Real.exp 1 ^ 2) ^ n * (n.factorial : ℝ) ^ 2)))) := by gcongr
        _ = (8 * ((n : ℝ) * n + 1)) * ((n : ℝ) ^ 3 * ((4 * Real.exp 1 ^ 2) ^ n *
              (n.factorial : ℝ) ^ 2)) := by ring
        _ ≤ (n : ℝ) ^ 4 * ((n : ℝ) ^ 3 * ((32 : ℝ) ^ n * (n.factorial : ℝ) ^ 2)) := by
            gcongr
        _ = (32 : ℝ) ^ n * (n : ℝ) ^ 7 * ((n.factorial : ℝ)) ^ 2 := by ring
    exact_mod_cast hR
  have := Nat.add_le_add h1 h2
  nlinarith
theorem exec_of_run_append {ι α : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (p : Proto ι α)
    (s : Rec ι) (tr₀ tc : List (Event ι)) (x : α) (s' : Rec ι)
    (h : Prog.run V o (p.run s) tr₀ = some ((x, s'), tr₀ ++ tc)) :
    exec V (fun t m ↦ o (tr₀ ++ t) m) p s = some (x, s', tc) := by
  have hs := run_shift V o (p.run s) tr₀ []
  rw [List.append_nil, h] at hs
  rcases h2 : Prog.run V (fun t m ↦ o (tr₀ ++ t) m) (p.run s) [] with _ | ⟨⟨x', s''⟩, tc'⟩
  · rw [h2] at hs; simp at hs
  · rw [h2] at hs
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨⟨rfl, rfl⟩, hh⟩ := hs
    have := List.append_cancel_left hh
    subst this
    exact (exec_iff V _ p s _ _ _).mpr h2

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

/-- The query budget of one iteration of Dominate. -/
def Qit (n : ℕ) : ℕ := n * (4 * n ^ 2) ^ (n + 1) + (2 * n ^ 2 * (n + 1) + 2) * (n ^ 3 * (n.factorial) ^ 2)

set_option maxHeartbeats 4000000 in
open scoped Classical in
theorem iteration {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) (hN : 3 ≤ N.card)
    (c : ι) (hc : c ∈ N) (C : Piece) (X : ι → Piece) (R : Piece) (t : Rec ι)
    (hI : DInv V N C X R t) (f : ℕ) (hf : 2 * N.card ^ 2 * (N.card + 1) ≤ f)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι)) :
    (∃ (X' : ι → Piece) (R' : Piece) (E : Finset ι) (t' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((dominateLoop N c (f + 1) X R).run t) tr₀ = some (((X', R', E), t'), tr) ∧
      IsPartialAlloc N C.toSet (fun i => (X' i).toSet) ∧
      R'.toSet = residue N C.toSet (fun i => (X' i).toSet) ∧
      EnvyFree V N (fun i => (X' i).toSet) ∧
      IsDominatedGroup V N (fun i => (X' i).toSet) R'.toSet E ∧
      queryCount tr ≤ queryCount tr₀ + Qit N.card) ∨
    (∃ (X' : ι → Piece) (R' : Piece) (t' : Rec ι) (tr : List (Event ι)),
      DInv V N C X' R' t' ∧ Phi V N X R < Phi V N X' R' ∧
      queryCount tr ≤ queryCount tr₀ + Qit N.card ∧
      Prog.run V o ((dominateLoop N c (f + 1) X R).run t) tr₀ =
        Prog.run V o ((dominateLoop N c f X' R').run t') tr) := by
  obtain ⟨hv, hRwf, hRal, hXwa, hXC, hXd, hRC, hEF⟩ := hI
  have hmeas : ∀ P : Piece, MeasurableSet P.toSet := piece_measurable
  have hrec : ∀ (s : Rec ι), s.Valid V N → ∀ i ∈ N, ∀ P : Piece, P.WF → s.Aligned P →
      s.pieceVal i P = (V i).value P.toSet := fun s hs i hi P hP hPa =>
    recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 V N s hs i hi P hP hPa
  have hXU : ∀ i ∈ N, (X i).toSet ⊆ ⋃ j ∈ N, (X j).toSet :=
    fun i hi => Set.subset_biUnion_of_mem (u := fun j => (X j).toSet) hi
  have hXR : ∀ i ∈ N, Disjoint (X i).toSet R.toSet := fun i hi => by
    rw [hRC]; exact Disjoint.mono_left (hXU i hi) Set.disjoint_sdiff_right
  have hRCsub : R.toSet ⊆ C.toSet := by rw [hRC]; exact Set.sdiff_subset
  -- Line 3: Core
  obtain ⟨Y, U, t1, tc, hcore, hpaY, hresU, hEFY, hcutY, hqcY, hv1, hsub1, hYwa, hUwf, hUal⟩ :=
    core_run V N (by omega) c hc R hRwf t hv hRal o tr₀
  have hYR : ∀ i ∈ N, (Y i).toSet ⊆ R.toSet := hpaY.1
  have hUR : U.toSet ⊆ R.toSet := by rw [hresU]; exact Set.sdiff_subset
  have hYU : ∀ i ∈ N, Disjoint (Y i).toSet U.toSet := fun i hi => by
    rw [hresU]; unfold residue
    exact Disjoint.mono_left (Set.subset_biUnion_of_mem (u := fun j => (Y j).toSet) hi)
      Set.disjoint_sdiff_right
  have hXY : ∀ i ∈ N, ∀ j ∈ N, Disjoint (X i).toSet (Y j).toSet :=
    fun i hi j hj => Disjoint.mono_right (hYR j hj) (hXR i hi)
  have hXal1 : ∀ i ∈ N, t1.Aligned (X i) := fun i hi => aligned_mono t t1 hsub1 _ (hXwa i hi).2
  let XY : ι → Piece := fun i => X i ++ Y i
  have hXYset : ∀ i, (XY i).toSet = (X i).toSet ∪ (Y i).toSet := fun i => toSet_append _ _
  have hXYwf : ∀ i ∈ N, (XY i).WF :=
    fun i hi => wf_append _ _ (hXwa i hi).1 (hYwa i hi).1 (hXY i hi i hi)
  have hXYal : ∀ i ∈ N, t1.Aligned (XY i) :=
    fun i hi => aligned_append t1 _ _ (hXal1 i hi) (hYwa i hi).2
  have hvXY : ∀ k, ∀ i ∈ N, (V k).value (XY i).toSet =
      (V k).value (X i).toSet + (V k).value (Y i).toSet := fun k i hi => by
    rw [hXYset, value_union _ (hmeas _) (hXY i hi i hi)]
  have hEFXY : EnvyFree V N (fun i => (XY i).toSet) := by
    intro i hi j hj
    show (V i).value (XY j).toSet ≤ (V i).value (XY i).toSet
    rw [hvXY i j hj, hvXY i i hi]
    have h1 := hEF i hi j hj; have h2 := hEFY i hi j hj
    simp only at h1 h2; linarith
  -- recorded domination tests are exact
  have hrecDom : ∀ E : Finset ι, E ⊆ N →
      (recDominatedGroup t1 N XY U E ↔ IsDominatedGroup V N (fun i => (XY i).toSet) U.toSet E) := by
    intro E hE
    unfold recDominatedGroup IsDominatedGroup recDominates Dominates
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨hE, h1, h2, fun i hi hiE j hj => ?_⟩
      have := h3 i hi hiE j hj
      rwa [hrec t1 hv1 i hi _ (hXYwf j (hE hj)) (hXYal j (hE hj)), hrec t1 hv1 i hi _ hUwf hUal,
        hrec t1 hv1 i hi _ (hXYwf i hi) (hXYal i hi)] at this
    · rintro ⟨-, h1, h2, h3⟩
      refine ⟨h1, h2, fun i hi hiE j hj => ?_⟩
      have := h3 i hi hiE j hj
      rwa [hrec t1 hv1 i hi _ (hXYwf j (hE hj)) (hXYal j (hE hj)), hrec t1 hv1 i hi _ hUwf hUal,
        hrec t1 hv1 i hi _ (hXYwf i hi) (hXYal i hi)]
  have hQ1 : N.card ^ 3 * (N.card.factorial) ^ 2 ≤ Qit N.card := by
    unfold Qit
    exact le_trans (Nat.le_mul_of_pos_left _ (by omega)) (Nat.le_add_left _ _)
  have hqcore : queryCount (tr₀ ++ tc) ≤ queryCount tr₀ + N.card ^ 3 * (N.card.factorial) ^ 2 := by
    rw [queryCount, List.countP_append]; exact Nat.add_le_add_left hqcY _
  let L : List (Finset ι) :=
    List.filter (fun E => decide (recDominatedGroup t1 N (fun i => X i ++ Y i) U E)) N.powerset.toList
  have hmemL : ∀ E, E ∈ L ↔ E ⊆ N ∧ recDominatedGroup t1 N (fun i => X i ++ Y i) U E := by
    intro E; simp only [L, List.mem_filter, Finset.mem_toList, Finset.mem_powerset,
      decide_eq_true_eq]
  have hfun : (fun i => (XY i).toSet) = (fun i => (X i).toSet ∪ (Y i).toSet) := funext hXYset
  by_cases hdom : ∃ E, IsDominatedGroup V N (fun i => (XY i).toSet) U.toSet E
  · -- Line 5: return
    left
    obtain ⟨E0, hE0⟩ := hdom
    have hLne : L ≠ [] := List.ne_nil_of_mem ((hmemL E0).mpr ⟨hE0.1, (hrecDom E0 hE0.1).mpr hE0⟩)
    obtain ⟨E, hEL, trE, hrunE, hqE⟩ := run_choose_ex V o L hLne t1 (tr₀ ++ tc)
    obtain ⟨hEN, hErec⟩ := (hmemL E).mp hEL
    refine ⟨XY, U, E, t1, trE, ?_, ⟨?_, ?_⟩, ?_, hEFXY, (hrecDom E hEN).mp hErec, ?_⟩
    · rw [dominateLoop, run_stbind, hcore]; dsimp only
      rw [run_stbind, run_get']; dsimp only
      rw [if_pos hLne, run_stbind, hrunE]; rfl
    · intro i hi
      show (XY i).toSet ⊆ C.toSet
      rw [hXYset]; exact Set.union_subset (hXC i hi) ((hYR i hi).trans hRCsub)
    · intro i hi j hj hij
      show Disjoint (XY i).toSet (XY j).toSet
      rw [hXYset, hXYset]
      exact Disjoint.union_left (Disjoint.union_right (hXd i hi j hj hij) (hXY i hi j hj))
        (Disjoint.union_right (hXY j hj i hi).symm (hpaY.2 i hi j hj hij))
    · rw [hresU, hRC]; unfold residue
      ext x
      simp only [Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and, hXYset,
        Set.mem_union]
      constructor
      · rintro ⟨⟨hxC, hxX⟩, hxY⟩; exact ⟨hxC, fun i hi h => h.elim (hxX i hi) (hxY i hi)⟩
      · rintro ⟨hxC, hx⟩
        exact ⟨⟨hxC, fun i hi h => hx i hi (Or.inl h)⟩, fun i hi h => hx i hi (Or.inr h)⟩
    · rw [hqE]; exact hqcore.trans (Nat.add_le_add_left hQ1 _)
  · -- no dominated group: Line 7
    right
    have hLnil : L = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro E hE
      obtain ⟨hEN, hErec⟩ := (hmemL E).mp hE
      exact hdom ⟨E, (hrecDom E hEN).mp hErec⟩
    have hexc := exec_of_run_append V o _ t tr₀ tc (Y, U) t1 hcore
    obtain ⟨hUpos, ts, hts2, htsn, is0, his0, js0, hjs0, hij0, π0, hπ0, hS1, hS2, hS3⟩ :=
      EnvyFreeCake104.Divide.lemma_5 V N hN X R (fun i hi => (hXwa i hi).1) hRwf hXd hXR hEF c hc
        t hv (fun i hi => (hXwa i hi).2) hRal _ Y U t1 tc hexc
        (by rintro ⟨E, hE⟩; rw [← hfun] at hE; exact hdom ⟨E, hE⟩)
    -- the Line 7 options are exactly the tuples satisfying (S1)-(S3)
    have hXwf : ∀ i ∈ N, (X i).WF := fun i hi => (hXwa i hi).1
    have hRal1 : t1.Aligned R := aligned_mono t t1 hsub1 _ hRal
    have hrX : ∀ i ∈ N, ∀ j ∈ N, t1.pieceVal i (X j) = (V i).value (X j).toSet :=
      fun i hi j hj => hrec t1 hv1 i hi _ (hXwf j hj) (hXal1 j hj)
    have hrY : ∀ i ∈ N, ∀ j ∈ N, t1.pieceVal i (Y j) = (V i).value (Y j).toSet :=
      fun i hi j hj => hrec t1 hv1 i hi _ (hYwa j hj).1 (hYwa j hj).2
    have hrU : ∀ i ∈ N, t1.pieceVal i U = (V i).value U.toSet :=
      fun i hi => hrec t1 hv1 i hi _ hUwf hUal
    have hrR : ∀ i ∈ N, t1.pieceVal i R = (V i).value R.toSet :=
      fun i hi => hrec t1 hv1 i hi _ hRwf hRal1
    have hmemO : ∀ (t' : ℕ) (is js : ι) (l' : List ι),
        (t', is, js, l') ∈ line7Options t1 N X R Y U ↔
        (2 ≤ t' ∧ t' < 2 + N.card) ∧ is ∈ N ∧ js ∈ N ∧ l' ∈ N.toList.permutations ∧
        (is ≠ js ∧ ¬ recDominates t1 X R is js ∧
          (∀ i ∈ N, t1.pieceVal i (Y i) - alphaOf N.card t' * t1.pieceVal i U ≤
            t1.pieceVal i (Y (permOfLists N.toList l' i))) ∧
          t1.pieceVal is (Y (permOfLists N.toList l' js)) ≤ t1.pieceVal is (Y is) -
            4 * (N.card : ℝ) ^ 2 * alphaOf N.card t' * t1.pieceVal is U) := by
      intro t' is js l'
      unfold line7Options
      simp only [List.mem_filter, List.pair_mem_product, List.mem_range'_1, Finset.mem_toList,
        decide_eq_true_eq]
      tauto
    have hOne : line7Options t1 N X R Y U ≠ [] := by
      apply List.ne_nil_of_mem (a := (ts, is0, js0, N.toList.map π0))
      rw [hmemO]
      have hpm := permOfLists_map N π0
      refine ⟨⟨hts2, by omega⟩, his0, hjs0, map_mem_permutations N π0 hπ0, hij0, ?_, ?_, ?_⟩
      · unfold recDominates; unfold Dominates at hS1
        rw [hrX is0 his0 js0 hjs0, hrR is0 his0, hrX is0 his0 is0 his0]; exact hS1
      · intro i hi
        rw [hpm i hi, hrY i hi i hi, hrU i hi, hrY i hi _ (hπ0.mapsTo hi)]; exact hS2 i hi
      · rw [hpm js0 hjs0, hrY is0 his0 _ (hπ0.mapsTo hjs0), hrY is0 his0 is0 his0, hrU is0 his0]
        exact hS3
    obtain ⟨⟨t', is, js, l'⟩, hoptO, tr2, hrunO, hq2⟩ :=
      run_choose_ex V o _ hOne t1 (tr₀ ++ tc)
    obtain ⟨⟨ht2, htn⟩, his, hjs, hl', hij, hS1r, hS2r, hS3r⟩ := (hmemO t' is js l').mp hoptO
    have hπ := permOfLists_bijOn N l' hl'
    have hπN : ∀ i ∈ N, permOfLists N.toList l' i ∈ N := fun i hi => hπ.mapsTo hi
    have hnR : (3 : ℝ) ≤ N.card := by exact_mod_cast hN
    have hαpos : 0 < alphaOf N.card t' := by unfold alphaOf; positivity
    have hαle : alphaOf N.card t' ≤ 1 / (6 * (N.card : ℝ) ^ 3) := by
      have h2 : alphaOf N.card t' ≤ alphaOf N.card 2 := by
        unfold alphaOf
        apply inv_anti₀ (by positivity)
        exact pow_le_pow_right₀ (by nlinarith) ht2
      refine h2.trans ?_
      unfold alphaOf
      rw [one_div]
      apply inv_anti₀ (by positivity)
      nlinarith [pow_pos (show (0:ℝ) < N.card by linarith) 3]
    -- true (S1)-(S3)
    have hS1' : ¬ Dominates V (fun i => (X i).toSet) R.toSet is js := by
      intro h; apply hS1r; unfold recDominates; unfold Dominates at h
      rw [hrX is his js hjs, hrR is his, hrX is his is his]; exact h
    have hS2' : ∀ i ∈ N, (V i).value (Y i).toSet - alphaOf N.card t' * (V i).value U.toSet ≤
        (V i).value (Y (permOfLists N.toList l' i)).toSet := by
      intro i hi; have := hS2r i hi
      rwa [hrY i hi i hi, hrU i hi, hrY i hi _ (hπN i hi)] at this
    have hS3' : (V is).value (Y (permOfLists N.toList l' js)).toSet ≤ (V is).value (Y is).toSet -
        4 * (N.card : ℝ) ^ 2 * alphaOf N.card t' * (V is).value U.toSet := by
      have := hS3r
      rwa [hrY is his _ (hπN js hjs), hrY is his is his, hrU is his] at this
    -- Line 8: Repair
    have hDset : ∀ i, (X i ++ Y (permOfLists N.toList l' i)).toSet =
        (X i).toSet ∪ (Y (permOfLists N.toList l' i)).toSet := fun i => toSet_append _ _
    have hDwf : ∀ i ∈ N, (X i ++ Y (permOfLists N.toList l' i)).WF := fun i hi =>
      wf_append _ _ (hXwf i hi) (hYwa _ (hπN i hi)).1 (hXY i hi _ (hπN i hi))
    have hDdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (X i ++ Y (permOfLists N.toList l' i)).toSet
        (X j ++ Y (permOfLists N.toList l' j)).toSet := by
      intro i hi j hj hij
      have hπij : permOfLists N.toList l' i ≠ permOfLists N.toList l' j :=
        fun h => hij (hπ.injOn hi hj h)
      rw [hDset, hDset]
      exact Disjoint.union_left (Disjoint.union_right (hXd i hi j hj hij) (hXY i hi _ (hπN j hj)))
        (Disjoint.union_right (hXY j hj _ (hπN i hi)).symm
          (hpaY.2 _ (hπN i hi) _ (hπN j hj) hπij))
    have hDU : ∀ i ∈ N, Disjoint (X i ++ Y (permOfLists N.toList l' i)).toSet U.toSet := by
      intro i hi; rw [hDset]
      exact Disjoint.union_left (Disjoint.mono_right hUR (hXR i hi)) (hYU _ (hπN i hi))
    have hDal : ∀ i ∈ N, t1.Aligned (X i ++ Y (permOfLists N.toList l' i)) := fun i hi =>
      aligned_append t1 _ _ (hXal1 i hi) (hYwa _ (hπN i hi)).2
    have hvD : ∀ k, ∀ i ∈ N, (V k).value (X i ++ Y (permOfLists N.toList l' i)).toSet =
        (V k).value (X i).toSet + (V k).value (Y (permOfLists N.toList l' i)).toSet :=
      fun k i hi => by rw [hDset, value_union _ (hmeas _) (hXY i hi _ (hπN i hi))]
    have halmost : ∀ i ∈ N, ∀ j ∈ N,
        (V i).value (X j ++ Y (permOfLists N.toList l' j)).toSet -
          alphaOf N.card t' * (V i).value U.toSet ≤
        (V i).value (X i ++ Y (permOfLists N.toList l' i)).toSet := by
      intro i hi j hj
      rw [hvD i j hj, hvD i i hi]
      have h1 := hEF i hi j hj; have h2 := hEFY i hi _ (hπN j hj); have h3 := hS2' i hi
      simp only at h1 h2; linarith
    obtain ⟨W, R', t2, tcr, hexr, hEFW, ⟨σ, Z, hσ, hZU, hZd, hWσ, hZval, hR'Z⟩, hqr⟩ :=
      EnvyFreeCake104.Divide.lemma_4 V N (by omega) (alphaOf N.card t') hαpos hαle
        (fun i => X i ++ Y (permOfLists N.toList l' i)) U hDwf hUwf hDdisj hDU hUpos halmost t1
        hv1 hDal hUal (fun s m ↦ o (tr2 ++ s) m)
    have hrunr := run_from_exec V o _ t1 tr2 (W, R') t2 tcr hexr
    obtain ⟨hv2, hsub2, hWwa, hR'wf, hR'al⟩ := EnvyFreeCake104.Divide.repair_invariants V N
      (fun i => X i ++ Y (permOfLists N.toList l' i)) U _ hDwf hUwf hDdisj hDU t1 hv1 hDal hUal
      o tr2 W R' t2 _ hrunr
    obtain ⟨hWd, hWsub, hR'eq⟩ := EnvyFreeCake104.Divide.repair_partition V N
      (fun i => X i ++ Y (permOfLists N.toList l' i)) U _ hDwf hUwf hDdisj hDU t1 hv1 hDal hUal
      o tr2 W R' t2 _ hrunr
    have hR'U : R'.toSet ⊆ U.toSet := by rw [hR'Z]; exact Set.sdiff_subset
    have hWR' : ∀ i ∈ N, Disjoint (W i).toSet R'.toSet := fun i hi => by
      rw [hR'eq]
      exact Disjoint.mono_left (Set.subset_biUnion_of_mem (u := fun j => (W j).toSet) hi)
        Set.disjoint_sdiff_right
    -- Lines 9-11: shrink
    have hK : (V is).value R'.toSet * (1 - 1 / (N.card : ℝ)) ^ (2 * N.card ^ 2 * (N.card + 1)) ≤
        alphaOf N.card t' * (V is).value U.toSet := by
      have hc1 := shrink_calls N.card t' hN (by omega)
      have hR'le := value_mono (V is) hR'U (hmeas _)
      have hR'0 := value_nonneg (V is) (hmeas R')
      have hp0 : 0 ≤ (1 - 1 / (N.card : ℝ)) ^ (2 * N.card ^ 2 * (N.card + 1)) := by
        apply pow_nonneg; rw [sub_nonneg, div_le_one (by linarith)]; linarith
      calc (V is).value R'.toSet * (1 - 1 / (N.card : ℝ)) ^ (2 * N.card ^ 2 * (N.card + 1))
          ≤ (V is).value U.toSet * alphaOf N.card t' := mul_le_mul hR'le hc1 hp0 (by linarith)
        _ = _ := by ring
    obtain ⟨W', R'', t3, tr4, hrunsh, hv3, hsub3, hW'wa, hR''wf, hR''al, hWW', hW'd, hR''eq,
        hEFW', hdiff, hR''small, hqsh⟩ :=
      EnvyFreeCake104.Divide.shrink_progress V N (by omega) is his (alphaOf N.card t') U hUwf
        (2 * N.card ^ 2 * (N.card + 1)) f hf W R' t2 o (tr2 ++ tcr)
        (fun i hi => (hWwa i hi).1) hR'wf hWd hWR' hEFW hv2 (fun i hi => (hWwa i hi).2) hR'al
        (aligned_mono t1 t2 hsub2 _ hUal) hK
    -- set-level facts
    have hDC : ∀ j ∈ N, (X j ++ Y (permOfLists N.toList l' j)).toSet ⊆ C.toSet := fun j hj => by
      rw [hDset]; exact Set.union_subset (hXC j hj) ((hYR _ (hπN j hj)).trans hRCsub)
    have hUD : U.toSet ∪ (⋃ j ∈ N, (X j ++ Y (permOfLists N.toList l' j)).toSet) = C.toSet := by
      apply Set.Subset.antisymm
      · exact Set.union_subset (hUR.trans hRCsub) (Set.iUnion₂_subset hDC)
      · intro x hxC
        by_cases hxX : x ∈ ⋃ j ∈ N, (X j).toSet
        · simp only [Set.mem_iUnion, exists_prop] at hxX
          obtain ⟨j, hj, hxj⟩ := hxX
          exact Or.inr (Set.mem_biUnion hj (by rw [hDset]; exact Or.inl hxj))
        · have hxR : x ∈ R.toSet := by rw [hRC]; exact ⟨hxC, hxX⟩
          by_cases hxY : x ∈ ⋃ k ∈ N, (Y k).toSet
          · simp only [Set.mem_iUnion, exists_prop] at hxY
            obtain ⟨k, hk, hxk⟩ := hxY
            obtain ⟨j, hj, hjk⟩ := hπ.surjOn hk
            refine Or.inr (Set.mem_biUnion hj ?_)
            rw [hDset]; right; rw [hjk]; exact hxk
          · left; rw [hresU]; exact ⟨hxR, hxY⟩
    have hWWsub : ∀ i ∈ N, (W i).toSet ⊆ (W' i).toSet := fun i hi => (hWW' i hi).1
    have hR''R' : R''.toSet ⊆ R'.toSet := by rw [hR''eq]; exact Set.sdiff_subset
    have hR''R : R''.toSet ⊆ R.toSet := hR''R'.trans (hR'U.trans hUR)
    have hW'C : ∀ i ∈ N, (W' i).toSet ⊆ C.toSet := by
      intro i hi
      refine (hWW' i hi).2.trans (Set.union_subset ((hWsub i hi).trans ?_) (hR'U.trans (hUR.trans hRCsub)))
      rw [hUD]
    have hR''C : R''.toSet = C.toSet \ ⋃ i ∈ N, (W' i).toSet := by
      rw [hR''eq, hR'eq, hUD]
      ext x
      simp only [Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and]
      constructor
      · rintro ⟨⟨hxC, -⟩, hx⟩; exact ⟨hxC, hx⟩
      · rintro ⟨hxC, hx⟩; exact ⟨⟨hxC, fun i hi h => hx i hi (hWWsub i hi h)⟩, hx⟩
    -- the domination count increases
    have hσN : ∀ j ∈ N, σ j ∈ N := fun j hj => hσ.mapsTo hj
    have hDZ : ∀ j ∈ N, Disjoint (X j ++ Y (permOfLists N.toList l' j)).toSet (Z j) :=
      fun j hj => Disjoint.mono_right (hZU j hj) (hDU j hj)
    have hmZ : ∀ j ∈ N, MeasurableSet (Z j) := by
      intro j hj
      have : Z j = (W (σ j)).toSet \ (X j ++ Y (permOfLists N.toList l' j)).toSet := by
        rw [hWσ j hj]; ext x
        simp only [Set.mem_sdiff, Set.mem_union]
        constructor
        · intro hx; exact ⟨Or.inr hx, fun h => Set.disjoint_left.mp (hDZ j hj) h hx⟩
        · rintro ⟨h | h, hn⟩
          · exact absurd h hn
          · exact h
      rw [this]; exact (hmeas _).diff (hmeas _)
    have hXW' : ∀ j ∈ N, (X j).toSet ⊆ (W' (σ j)).toSet := by
      intro j hj
      refine Set.Subset.trans ?_ (hWWsub _ (hσN j hj))
      rw [hWσ j hj, hDset]
      exact Set.subset_union_left.trans Set.subset_union_left
    have hW'X : ∀ j ∈ N, (W' (σ j)).toSet ⊆ (X j).toSet ∪ (R.toSet \ R''.toSet) := by
      intro j hj x hx
      have hxR'' : x ∉ R''.toSet := by
        rw [hR''eq]; intro h; exact h.2 (Set.mem_biUnion (hσN j hj) hx)
      rcases (hWW' _ (hσN j hj)).2 hx with h | h
      · rw [hWσ j hj, hDset] at h
        rcases h with (h | h) | h
        · exact Or.inl h
        · exact Or.inr ⟨hYR _ (hπN j hj) h, hxR''⟩
        · exact Or.inr ⟨hUR (hZU j hj h), hxR''⟩
      · exact Or.inr ⟨hUR (hR'U h), hxR''⟩
    have hgap : ∀ i ∈ N, ∀ j ∈ N,
        (V i).value R.toSet ≤ (V i).value (X i).toSet - (V i).value (X j).toSet →
        (V i).value R''.toSet ≤ (V i).value (W' i).toSet - (V i).value (W' (σ j)).toSet := by
      intro i hi j hj hdom
      have h1 := value_mono (V i) (hW'X j hj) ((hmeas _).union ((hmeas _).diff (hmeas _)))
      have h2 := value_union_le (V i) (hmeas (X j)) ((hmeas R).diff (hmeas R''))
      have h3 := value_sdiff (V i) (hmeas R) (hmeas R'') hR''R
      have h4 : (V i).value (W' (σ i)).toSet ≤ (V i).value (W' i).toSet := hEFW' i hi _ (hσN i hi)
      have h5 := value_mono (V i) (hXW' i hi) (hmeas _)
      linarith
    have hnew : (V is).value R''.toSet ≤
        (V is).value (W' is).toSet - (V is).value (W' (σ js)).toSet := by
      have hU0 : 0 ≤ alphaOf N.card t' * (V is).value U.toSet :=
        mul_nonneg hαpos.le (value_nonneg _ (hmeas _))
      have hd := hdiff is his (σ js) (hσN js hjs)
      have e1 : (V is).value (W (σ is)).toSet ≤ (V is).value (W is).toSet :=
        hEFW is his _ (hσN is his)
      have e2 : (V is).value (X is ++ Y (permOfLists N.toList l' is)).toSet ≤
          (V is).value (W (σ is)).toSet := by
        apply value_mono _ _ (hmeas _); rw [hWσ is his]; exact Set.subset_union_left
      have e3 : (V is).value (W (σ js)).toSet = (V is).value (X js).toSet +
          (V is).value (Y (permOfLists N.toList l' js)).toSet + (V is).value (Z js) := by
        rw [hWσ js hjs, value_union _ (hmZ js hjs) (hDZ js hjs), hvD is js hjs]
      have e4 := hvD is is his
      have e5 := hEF is his js hjs
      have e6 := hS2' is his
      have e7 := hZval is his js hjs
      have hn2 : (2 : ℝ) ≤ (N.card : ℝ) ^ 2 := by nlinarith
      simp only at e5
      nlinarith
    have hPhi : Phi V N X R < Phi V N W' R'' := by
      unfold Phi
      apply Finset.sum_lt_sum
      · intro i hi
        rw [← Finset.card_image_of_injOn (fun a ha b hb h => hσ.injOn
          (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 h)]
        apply Finset.card_le_card
        intro y hy
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨hjN, hjd⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨hσN j hjN, hgap i hi j hjN hjd⟩
      · refine ⟨is, his, ?_⟩
        rw [← Finset.card_image_of_injOn (fun a ha b hb h => hσ.injOn
          (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 h)]
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨σ js, ?_, ?_⟩
        · intro y hy
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
          obtain ⟨hjN, hjd⟩ := Finset.mem_filter.mp hj
          exact Finset.mem_filter.mpr ⟨hσN j hjN, hgap is his j hjN hjd⟩
        · exact Finset.mem_filter.mpr ⟨hσN js hjs, hnew⟩
        · intro hy
          obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp hy
          obtain ⟨hjN, hjd⟩ := Finset.mem_filter.mp hj
          have := hσ.injOn hjN hjs hjeq
          subst this
          apply hS1'; unfold Dominates; simp only; linarith
    -- query count
    have hqr' : queryCount tcr ≤ N.card * (4 * N.card ^ 2) ^ (N.card + 1) +
        N.card ^ 3 * (N.card.factorial) ^ 2 := by
      have hal := alpha_lower N.card t' (by omega) (by omega)
      have hinv : (N.card : ℝ) / alphaOf N.card t' ≤ N.card * (4 * (N.card : ℝ) ^ 2) ^ (N.card + 1) := by
        rw [div_le_iff₀ hαpos]
        have hq0 : (0 : ℝ) < (4 * (N.card : ℝ) ^ 2) ^ (N.card + 1) := by positivity
        have : 1 ≤ (4 * (N.card : ℝ) ^ 2) ^ (N.card + 1) * alphaOf N.card t' := by
          have := mul_le_mul_of_nonneg_left hal hq0.le
          rwa [mul_inv_cancel₀ hq0.ne'] at this
        calc (N.card : ℝ) = N.card * 1 := by ring
          _ ≤ N.card * ((4 * (N.card : ℝ) ^ 2) ^ (N.card + 1) * alphaOf N.card t') :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := by ring
      have key : (queryCount tcr : ℝ) ≤ (N.card : ℝ) * (4 * (N.card : ℝ) ^ 2) ^ (N.card + 1) +
          (N.card : ℝ) ^ 3 * ((N.card.factorial : ℕ) : ℝ) ^ 2 :=
        le_trans hqr (add_le_add hinv le_rfl)
      have hcast : ((N.card * (4 * N.card ^ 2) ^ (N.card + 1) + N.card ^ 3 * (N.card.factorial) ^ 2 :
          ℕ) : ℝ) = (N.card : ℝ) * (4 * (N.card : ℝ) ^ 2) ^ (N.card + 1) +
          (N.card : ℝ) ^ 3 * ((N.card.factorial : ℕ) : ℝ) ^ 2 := by norm_cast
      exact Nat.cast_le.mp (by rw [hcast]; exact key)
    refine ⟨W', R'', t3, tr4, ⟨hv3, hR''wf, hR''al, hW'wa, hW'C, hW'd, hR''C, hEFW'⟩, hPhi, ?_, ?_⟩
    · have q1 : queryCount (tr2 ++ tcr) = queryCount tr2 + queryCount tcr := List.countP_append ..
      have hq2' : queryCount tr2 ≤ queryCount tr₀ + N.card ^ 3 * (N.card.factorial) ^ 2 :=
        hq2 ▸ hqcore
      have hfin : queryCount tr4 ≤ (queryCount tr₀ + N.card ^ 3 * (N.card.factorial) ^ 2) +
          (N.card * (4 * N.card ^ 2) ^ (N.card + 1) + N.card ^ 3 * (N.card.factorial) ^ 2) +
          2 * N.card ^ 2 * (N.card + 1) * (N.card ^ 3 * (N.card.factorial) ^ 2) := by
        calc queryCount tr4 ≤ queryCount (tr2 ++ tcr) +
              2 * N.card ^ 2 * (N.card + 1) * (N.card ^ 3 * (N.card.factorial) ^ 2) := hqsh
          _ = queryCount tr2 + queryCount tcr +
              2 * N.card ^ 2 * (N.card + 1) * (N.card ^ 3 * (N.card.factorial) ^ 2) := by rw [q1]
          _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add hq2' hqr') _
      refine hfin.trans (le_of_eq ?_)
      unfold Qit
      generalize N.card * (4 * N.card ^ 2) ^ (N.card + 1) = A
      generalize N.card ^ 3 * (N.card.factorial) ^ 2 = Q
      generalize 2 * N.card ^ 2 * (N.card + 1) = K
      ring
    · rw [dominateLoop, run_stbind, hcore]; dsimp only
      rw [run_stbind, run_get']; dsimp only
      rw [if_neg (fun h => h hLnil), run_stbind, hrunO]; dsimp only
      rw [run_stbind, hrunr]; dsimp only
      rw [run_stbind, hrunsh]

open scoped Classical in
theorem loop_main {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) (hN : 3 ≤ N.card)
    (c : ι) (hc : c ∈ N) (C : Piece) : ∀ (d : ℕ) (X : ι → Piece) (R : Piece) (t : Rec ι)
    (tr₀ : List (Event ι)) (f : ℕ) (o : ChoiceOracle ι),
    DInv V N C X R t → N.card * N.card - Phi V N X R ≤ d →
    2 * N.card ^ 2 * (N.card + 1) + d + 1 ≤ f →
    ∃ (X' : ι → Piece) (R' : Piece) (E : Finset ι) (t' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((dominateLoop N c f X R).run t) tr₀ = some (((X', R', E), t'), tr) ∧
      IsPartialAlloc N C.toSet (fun i => (X' i).toSet) ∧
      R'.toSet = residue N C.toSet (fun i => (X' i).toSet) ∧
      EnvyFree V N (fun i => (X' i).toSet) ∧
      IsDominatedGroup V N (fun i => (X' i).toSet) R'.toSet E ∧
      queryCount tr ≤ queryCount tr₀ + (d + 1) * Qit N.card := by
  intro d
  induction d with
  | zero =>
    intro X R t tr₀ f o hI hd hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rcases iteration V N hN c hc C X R t hI g (by omega) o tr₀ with
      ⟨X', R', E, t', tr, h1, h2, h3, h4, h5, h6⟩ | ⟨X', R', t', tr, hI', hP, -, -⟩
    · exact ⟨X', R', E, t', tr, h1, h2, h3, h4, h5, by omega⟩
    · have := Phi_le V N X' R'; omega
  | succ d ih =>
    intro X R t tr₀ f o hI hd hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rcases iteration V N hN c hc C X R t hI g (by omega) o tr₀ with
      ⟨X', R', E, t', tr, h1, h2, h3, h4, h5, h6⟩ | ⟨X', R', t', tr, hI', hP, hq, heq⟩
    · exact ⟨X', R', E, t', tr, h1, h2, h3, h4, h5, by nlinarith⟩
    · have hle := Phi_le V N X' R'
      obtain ⟨X'', R'', E, t'', tr', h1, h2, h3, h4, h5, h6⟩ :=
        ih X' R' t' tr g o hI' (by omega) (by omega)
      refine ⟨X'', R'', E, t'', tr', heq.trans h1, h2, h3, h4, h5, ?_⟩
      calc queryCount tr' ≤ queryCount tr + (d + 1) * Qit N.card := h6
        _ ≤ queryCount tr₀ + Qit N.card + (d + 1) * Qit N.card := by omega
        _ = queryCount tr₀ + (d + 1 + 1) * Qit N.card := by ring

end L1Aux

open L1Aux in
open scoped Classical in
theorem solution {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 3 ≤ N.card) (C : Piece) (hC : C.WF)
    (s : Rec ι) (hs : s.Valid V N) (hCs : s.Aligned C) (o : ChoiceOracle ι) :
    ∃ (fuel : ℕ) (X : ι → Piece) (R : Piece) (E : Finset ι) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (dominate fuel N C) s = some ((X, R, E), s', tr) ∧
      IsPartialAlloc N C.toSet (fun i => (X i).toSet) ∧
      R.toSet = residue N C.toSet (fun i => (X i).toSet) ∧
      EnvyFree V N (fun i => (X i).toSet) ∧
      IsDominatedGroup V N (fun i => (X i).toSet) R.toSet E ∧
      queryCount tr ≤ 32 ^ N.card * N.card ^ 7 * (N.card.factorial) ^ 2 := by
  have hnil : N.toList ≠ [] := by
    intro h; rw [Finset.toList_eq_nil] at h; subst h; simp at hN
  obtain ⟨c, hcL, tr1, hrun1, hq1⟩ := run_choose_ex V o N.toList hnil s []
  have hc : c ∈ N := Finset.mem_toList.mp hcL
  have hI : DInv V N C (fun _ => []) C s := by
    refine ⟨hs, hC, hCs, fun i _ => ⟨wf_nil, fun I hI => by simp at hI⟩, fun i _ => by simp [toSet_nil],
      fun i _ j _ _ => by simp [toSet_nil], by simp [toSet_nil], ?_⟩
    intro i _ j _; simp
  obtain ⟨X, R, E, s', tr, hrun, h2, h3, h4, h5, h6⟩ :=
    loop_main V N hN c hc C (N.card * N.card) (fun _ => []) C s tr1
      (N.card * N.card + 2 * N.card ^ 2 * (N.card + 1) + 1) o hI (by omega) (by omega)
  refine ⟨N.card * N.card + 2 * N.card ^ 2 * (N.card + 1) + 1, X, R, E, s', tr, ?_, h2, h3, h4,
    h5, ?_⟩
  · rw [exec_iff]; unfold dominate; rw [run_stbind, hrun1]; exact hrun
  · rw [hq1] at h6
    have hb := total_bound N.card hN
    simp only [queryCount, List.countP_nil, zero_add] at h6
    unfold Qit at h6
    unfold queryCount
    exact h6.trans hb
