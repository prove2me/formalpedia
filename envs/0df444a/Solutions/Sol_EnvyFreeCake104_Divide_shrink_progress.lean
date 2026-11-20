-- Prove2me | solution 1 for EnvyFreeCake104.Divide.shrink_progress
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T17:27:05.539072+00:00
-- url     : https://prove2.me/submissions/35c63eb2-88df-4f4f-8178-1fb8788c62f3

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_lemma_3
import Theorems.Thm_EnvyFreeCake104_Divide_core_invariants
import Theorems.Thm_EnvyFreeCake104_Divide_recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1

open EnvyFreeCake104.Divide

namespace SHAux

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
open scoped Classical in
theorem shrink_main {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 2 ≤ N.card) (istar : ι) (hi : istar ∈ N) (α : ℝ) (U : Piece) (hU : U.WF) :
    ∀ (K fuel : ℕ), K ≤ fuel → ∀ (W : ι → Piece) (R' : Piece) (s : Rec ι)
      (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
      (∀ i ∈ N, (W i).WF) → R'.WF →
      (∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (W i).toSet (W j).toSet) →
      (∀ i ∈ N, Disjoint (W i).toSet R'.toSet) →
      EnvyFree V N (fun i => (W i).toSet) →
      s.Valid V N → (∀ i ∈ N, s.Aligned (W i)) → s.Aligned R' → s.Aligned U →
      (V istar).value R'.toSet * (1 - 1 / (N.card : ℝ)) ^ K ≤ α * (V istar).value U.toSet →
      ∃ (W' : ι → Piece) (R'' : Piece) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((shrink N istar α U fuel W R').run s) tr₀ =
          some (((W', R''), s'), tr) ∧
        s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ (∀ i ∈ N, (W' i).WF ∧ s'.Aligned (W' i)) ∧
        R''.WF ∧ s'.Aligned R'' ∧
        (∀ i ∈ N, (W i).toSet ⊆ (W' i).toSet ∧ (W' i).toSet ⊆ (W i).toSet ∪ R'.toSet) ∧
        (∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (W' i).toSet (W' j).toSet) ∧
        R''.toSet = R'.toSet \ ⋃ i ∈ N, (W' i).toSet ∧
        EnvyFree V N (fun i => (W' i).toSet) ∧
        (∀ i ∈ N, ∀ j ∈ N, (V i).value (W i).toSet - (V i).value (W j).toSet ≤
          (V i).value (W' i).toSet - (V i).value (W' j).toSet) ∧
        (V istar).value R''.toSet ≤ α * (V istar).value U.toSet ∧
        queryCount tr ≤ queryCount tr₀ + K * (N.card ^ 3 * (N.card.factorial) ^ 2) := by
  have hmeas : ∀ P : Piece, MeasurableSet P.toSet := piece_measurable
  have hrec : ∀ (t : Rec ι), t.Valid V N → ∀ i ∈ N, ∀ P : Piece, P.WF → t.Aligned P →
      t.pieceVal i P = (V i).value P.toSet := fun t ht i hi P hP hPa =>
    recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 V N t ht i hi P hP hPa
  have hn : (0 : ℝ) < N.card := by exact_mod_cast (show 0 < N.card by omega)
  intro K
  induction K with
  | zero =>
    intro fuel _ W R' s o tr₀ hW hR' hWd hWR hEF hs hWs hRs hUs hK
    simp only [pow_zero, mul_one] at hK
    refine ⟨W, R', s, tr₀, ?_, hs, subset_rfl, fun i hi => ⟨hW i hi, hWs i hi⟩, hR', hRs,
      fun i _ => ⟨subset_rfl, Set.subset_union_left⟩, hWd, ?_, hEF, fun i _ j _ => le_rfl, hK,
      by simp⟩
    · rw [shrink.eq_def, run_stbind, run_get']
      dsimp only
      rw [if_neg (by rw [hrec s hs istar hi U hU hUs, hrec s hs istar hi R' hR' hRs]; linarith)]
      rfl
    · ext x
      simp only [Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and]
      exact ⟨fun h => ⟨h, fun i hi hx => Set.disjoint_left.mp (hWR i hi) hx h⟩, fun h => h.1⟩
  | succ K ih =>
    intro fuel hfuel W R' s o tr₀ hW hR' hWd hWR hEF hs hWs hRs hUs hK
    have hvU := hrec s hs istar hi U hU hUs
    have hvR := hrec s hs istar hi R' hR' hRs
    by_cases hcond : α * (V istar).value U.toSet < (V istar).value R'.toSet
    · obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
      obtain ⟨F, R2, s1, tc, hcore, hpa, hres, hEFF, hcut, hqc, hs1, hsub1, hFwf, hR2wf, hR2al⟩ :=
        core_run V N hN istar hi R' hR' s hs hRs o tr₀
      -- the cutter's residue shrinks by a factor 1 - 1/n
      have hpart := value_partition (V istar) N R'.toSet (fun i => (F i).toSet) R2.toSet
        (fun i => hmeas _) (hmeas _) hpa hres
      have hrest : 0 ≤ ∑ i ∈ N.erase istar, (V istar).value (F i).toSet :=
        Finset.sum_nonneg (fun i _ => value_nonneg _ (hmeas _))
      rw [← Finset.add_sum_erase N _ hi, hcut] at hpart
      have hR2le : (V istar).value R2.toSet ≤
          (V istar).value R'.toSet * (1 - 1 / (N.card : ℝ)) := by
        have : (V istar).value R'.toSet / N.card = (V istar).value R'.toSet * (1 / N.card) := by
          ring
        rw [this] at hpart; nlinarith
      have h01 : 0 ≤ 1 - 1 / (N.card : ℝ) := by
        rw [sub_nonneg, div_le_one hn]; exact_mod_cast (show 1 ≤ N.card by omega)
      have hFR : ∀ i ∈ N, (F i).toSet ⊆ R'.toSet := hpa.1
      have hR2R : R2.toSet ⊆ R'.toSet := by rw [hres]; exact Set.sdiff_subset
      have hWF : ∀ i ∈ N, ∀ j ∈ N, Disjoint (W i).toSet (F j).toSet :=
        fun i hi j hj => Disjoint.mono_right (hFR j hj) (hWR i hi)
      let W1 : ι → Piece := fun i => W i ++ F i
      have hW1set : ∀ i, (W1 i).toSet = (W i).toSet ∪ (F i).toSet := fun i => toSet_append _ _
      have hvW1 : ∀ k, ∀ i ∈ N, (V k).value (W1 i).toSet =
          (V k).value (W i).toSet + (V k).value (F i).toSet := fun k i hi => by
        rw [hW1set, value_union _ (hmeas _) (hWF i hi i hi)]
      have hFR2 : ∀ i ∈ N, Disjoint (F i).toSet R2.toSet := by
        intro i hi; rw [hres]; unfold residue
        exact Disjoint.mono_left (Set.subset_biUnion_of_mem (u := fun j => (F j).toSet) hi)
          Set.disjoint_sdiff_right
      obtain ⟨W', R'', s', tr, hr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
        ih g (by omega) W1 R2 s1 o (tr₀ ++ tc)
          (fun i hi => wf_append _ _ (hW i hi) (hFwf i hi).1 (hWF i hi i hi)) hR2wf
          (by intro i hi j hj hij
              rw [hW1set, hW1set]
              exact Disjoint.union_left (Disjoint.union_right (hWd i hi j hj hij) (hWF i hi j hj))
                (Disjoint.union_right (hWF j hj i hi).symm (hpa.2 i hi j hj hij)))
          (by intro i hi
              rw [hW1set]
              exact Disjoint.union_left (Disjoint.mono_right hR2R (hWR i hi)) (hFR2 i hi))
          (by intro i hi j hj
              show (V i).value (W1 j).toSet ≤ (V i).value (W1 i).toSet
              rw [hvW1 i j hj, hvW1 i i hi]
              linarith [hEF i hi j hj, hEFF i hi j hj])
          hs1 (fun i hi => aligned_append s1 _ _ (aligned_mono s s1 hsub1 _ (hWs i hi)) (hFwf i hi).2)
          hR2al (aligned_mono s s1 hsub1 _ hUs)
          (by calc (V istar).value R2.toSet * (1 - 1 / (N.card : ℝ)) ^ K
                ≤ (V istar).value R'.toSet * (1 - 1 / (N.card : ℝ)) *
                    (1 - 1 / (N.card : ℝ)) ^ K :=
                  mul_le_mul_of_nonneg_right hR2le (pow_nonneg h01 _)
              _ = (V istar).value R'.toSet * (1 - 1 / (N.card : ℝ)) ^ (K + 1) := by ring
              _ ≤ _ := hK)
      refine ⟨W', R'', s', tr, ?_, h1, hsub1.trans h2, h3, h4, h5, ?_, h7, ?_, h9, ?_, h11, ?_⟩
      · rw [shrink.eq_def, run_stbind, run_get']
        dsimp only
        rw [if_pos (by rw [hvU, hvR]; exact hcond)]
        try dsimp only
        rw [run_stbind, hcore]
        exact hr
      · intro i hi
        obtain ⟨a1, a2⟩ := h6 i hi
        refine ⟨(hW1set i ▸ Set.subset_union_left).trans a1, a2.trans ?_⟩
        rw [hW1set]
        exact Set.union_subset (Set.union_subset Set.subset_union_left
          ((hFR i hi).trans Set.subset_union_right)) (hR2R.trans Set.subset_union_right)
      · rw [h8]
        ext x
        simp only [Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and]
        constructor
        · rintro ⟨hx, hnx⟩; exact ⟨hR2R hx, hnx⟩
        · rintro ⟨hx, hnx⟩
          refine ⟨?_, hnx⟩
          rw [hres]; unfold residue
          refine ⟨hx, ?_⟩
          simp only [Set.mem_iUnion, exists_prop, not_exists, not_and]
          intro i hi hxi
          exact hnx i hi ((h6 i hi).1 (by rw [hW1set]; exact Or.inr hxi))
      · intro i hi j hj
        have := h10 i hi j hj
        rw [hvW1 i i hi, hvW1 i j hj] at this
        linarith [hEFF i hi j hj]
      · have : queryCount (tr₀ ++ tc) = queryCount tr₀ + queryCount tc := List.countP_append ..
        rw [this] at h12
        have hB : 0 ≤ N.card ^ 3 * (N.card.factorial) ^ 2 := Nat.zero_le _
        nlinarith
    · -- the loop stops at once
      push Not at hcond
      refine ⟨W, R', s, tr₀, ?_, hs, subset_rfl, fun i hi => ⟨hW i hi, hWs i hi⟩, hR', hRs,
        fun i _ => ⟨subset_rfl, Set.subset_union_left⟩, hWd, ?_, hEF, fun i _ j _ => le_rfl, hcond,
        by omega⟩
      · rw [shrink.eq_def, run_stbind, run_get']
        dsimp only
        rw [if_neg (by rw [hvU, hvR]; linarith)]
        rfl
      · ext x
        simp only [Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and]
        exact ⟨fun h => ⟨h, fun i hi hx => Set.disjoint_left.mp (hWR i hi) hx h⟩, fun h => h.1⟩

end SHAux

open SHAux in
open scoped Classical in
theorem solution {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 2 ≤ N.card) (istar : ι) (hi : istar ∈ N) (α : ℝ) (U : Piece) (hU : U.WF) :
    ∀ (K fuel : ℕ), K ≤ fuel → ∀ (W : ι → Piece) (R' : Piece) (s : Rec ι)
      (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
      (∀ i ∈ N, (W i).WF) → R'.WF →
      (∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (W i).toSet (W j).toSet) →
      (∀ i ∈ N, Disjoint (W i).toSet R'.toSet) →
      EnvyFree V N (fun i => (W i).toSet) →
      s.Valid V N → (∀ i ∈ N, s.Aligned (W i)) → s.Aligned R' → s.Aligned U →
      (V istar).value R'.toSet * (1 - 1 / (N.card : ℝ)) ^ K ≤ α * (V istar).value U.toSet →
      ∃ (W' : ι → Piece) (R'' : Piece) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((shrink N istar α U fuel W R').run s) tr₀ =
          some (((W', R''), s'), tr) ∧
        s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ (∀ i ∈ N, (W' i).WF ∧ s'.Aligned (W' i)) ∧
        R''.WF ∧ s'.Aligned R'' ∧
        (∀ i ∈ N, (W i).toSet ⊆ (W' i).toSet ∧ (W' i).toSet ⊆ (W i).toSet ∪ R'.toSet) ∧
        (∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (W' i).toSet (W' j).toSet) ∧
        R''.toSet = R'.toSet \ ⋃ i ∈ N, (W' i).toSet ∧
        EnvyFree V N (fun i => (W' i).toSet) ∧
        (∀ i ∈ N, ∀ j ∈ N, (V i).value (W i).toSet - (V i).value (W j).toSet ≤
          (V i).value (W' i).toSet - (V i).value (W' j).toSet) ∧
        (V istar).value R''.toSet ≤ α * (V istar).value U.toSet ∧
        queryCount tr ≤ queryCount tr₀ + K * (N.card ^ 3 * (N.card.factorial) ^ 2) :=
  shrink_main V N hN istar hi α U hU
