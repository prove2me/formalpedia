-- Prove2me | solution 1 for EnvyFreeCake104.Divide.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T17:09:35.432329+00:00
-- url     : https://prove2.me/submissions/a40271ed-993f-492d-ae23-19e32f6c2d4f

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_lemma_1
import Theorems.Thm_EnvyFreeCake104_Divide_dominate_invariants
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
import Theorems.Thm_EnvyFreeCake104_Divide_cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
import Theorems.Thm_EnvyFreeCake104_Divide_recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_query_bound__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1

open EnvyFreeCake104.Divide

namespace T2Aux

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
theorem shrink_mono {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) (i : ι)
    (α : ℝ) (U : Piece) : ∀ (f f' : ℕ), f ≤ f' → ∀ W R',
    PRef V (shrink N i α U f W R') (shrink N i α U f' W R') := by
  intro f
  induction f with
  | zero =>
    intro f' _ W R'
    rw [shrink.eq_def, shrink.eq_def]
    refine pref_bind V (pref_refl V _) (fun st => ?_)
    split_ifs
    · intro s o tr r h; simp [run_fail'] at h
    · exact pref_refl V _
  | succ f ih =>
    intro f' hf W R'
    obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    rw [shrink.eq_def, shrink.eq_def]
    refine pref_bind V (pref_refl V _) (fun st => ?_)
    split_ifs
    · dsimp only
      refine pref_bind V (pref_refl V _) (fun x => ?_)
      obtain ⟨F, R''⟩ := x
      exact ih g (by omega) _ _
    · exact pref_refl V _

theorem dominateLoop_mono {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (c : ι) : ∀ (f f' : ℕ), f ≤ f' → ∀ X R,
    PRef V (dominateLoop N c f X R) (dominateLoop N c f' X R) := by
  intro f
  induction f with
  | zero =>
    intro f' _ X R s o tr r h
    rw [dominateLoop] at h; simp [run_fail'] at h
  | succ f ih =>
    intro f' hf X R
    obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    rw [dominateLoop, dominateLoop]
    refine pref_bind V (pref_refl V _) (fun x => ?_)
    obtain ⟨Y, U⟩ := x
    dsimp only
    refine pref_bind V (pref_refl V _) (fun st => ?_)
    try dsimp only
    split_ifs
    · exact pref_refl V _
    · refine pref_bind V (pref_refl V _) (fun x => ?_)
      obtain ⟨t, istar, jstar, l'⟩ := x
      try dsimp only
      refine pref_bind V (pref_refl V _) (fun x => ?_)
      obtain ⟨W, R'⟩ := x
      try dsimp only
      refine pref_bind V (shrink_mono V N _ _ _ f g (by omega) _ _) (fun x => ?_)
      obtain ⟨W', R''⟩ := x
      exact ih g (by omega) _ _

theorem dominate_mono {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) (C : Piece)
    (f f' : ℕ) (hf : f ≤ f') : PRef V (dominate f N C) (dominate f' N C) := by
  unfold dominate
  exact pref_bind V (pref_refl V _) (fun c => dominateLoop_mono V N c f f' hf _ _)

theorem divide_mono {ι : Type} [DecidableEq ι] (V : ι → Valuation) : ∀ (f f' : ℕ), f ≤ f' →
    ∀ (N : Finset ι) (C : Piece), PRef V (divide f N C) (divide f' N C) := by
  intro f
  induction f with
  | zero =>
    intro f' _ N C s o tr r h
    rw [divide] at h; simp [run_fail'] at h
  | succ f ih =>
    intro f' hf N C
    obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    rw [divide, divide]
    split_ifs
    · exact pref_refl V _
    · exact pref_refl V _
    · exact pref_refl V _
    · refine pref_bind V (dominate_mono V N C f g (by omega)) (fun x => ?_)
      obtain ⟨X, R, E⟩ := x
      exact pref_bind V (ih g (by omega) E R) (fun _ => pref_refl V _)
def B (n : ℕ) : ℕ := 32 ^ n * n ^ 7 * (n.factorial) ^ 2

theorem B_succ (m : ℕ) : 32 * B m ≤ B (m + 1) := by
  unfold B
  have h1 : m ^ 7 ≤ (m + 1) ^ 7 := Nat.pow_le_pow_left (by omega) 7
  have h3 : m.factorial ^ 2 ≤ (m + 1).factorial ^ 2 :=
    Nat.pow_le_pow_left (Nat.factorial_le (by omega)) 2
  calc 32 * (32 ^ m * m ^ 7 * m.factorial ^ 2) = 32 ^ m * 32 * (m ^ 7 * m.factorial ^ 2) := by ring
    _ ≤ 32 ^ m * 32 * ((m + 1) ^ 7 * (m + 1).factorial ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h3)
    _ = 32 ^ (m + 1) * (m + 1) ^ 7 * (m + 1).factorial ^ 2 := by ring

theorem B_mono : Monotone B :=
  monotone_nat_of_le_succ (fun m => le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) (B_succ m))

open scoped Classical in
theorem part1 {ι : Type} [DecidableEq ι] (V : ι → Valuation) : ∀ n : ℕ, ∀ (N : Finset ι),
    N.card = n → N.Nonempty → ∀ C : Piece, C.WF → ∀ s : Rec ι, s.Valid V N → s.Aligned C →
    ∀ o : ChoiceOracle ι, ∃ (fuel : ℕ) (A : ι → Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (divide fuel N C) s = some (A, s', tr) ∧
      IsPartialAlloc N C.toSet (fun i => (A i).toSet) ∧
      IsComplete N C.toSet (fun i => (A i).toSet) ∧
      EnvyFree V N (fun i => (A i).toSet) ∧
      queryCount tr ≤ 2 * B N.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hNn hNne C hC s hs hCs o
  have hmeas : ∀ P : Piece, MeasurableSet P.toSet := piece_measurable
  by_cases h1 : N.card = 1
  · -- one agent
    obtain ⟨x, hx, tr1, hrun1, hq1⟩ := run_choose_ex V o N.toList
      (by intro h; rw [Finset.toList_eq_nil] at h; subst h; simp at hNne) s []
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    have hxa : x = a := by simpa using hx
    subst hxa
    refine ⟨1, fun j => if j = x then C else [], s, tr1, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [exec_iff, divide, if_pos h1, run_stbind, hrun1]; rfl
    · intro i hi; rw [Finset.mem_singleton] at hi; subst hi; simp
    · intro i hi j hj hij
      rw [Finset.mem_singleton] at hi hj; exact absurd (hi.trans hj.symm) hij
    · simp [EnvyFreeCake104.Divide.IsComplete]
    · intro i hi j hj
      rw [Finset.mem_singleton] at hi hj; subst hi; subst hj; exact le_rfl
    · rw [hq1]; simp [queryCount]
  by_cases h2 : N.card = 2
  · -- Cut-and-Choose
    have hnil : N.toList ≠ [] := by
      intro h; rw [Finset.toList_eq_nil] at h; subst h; simp at hNne
    obtain ⟨first, hfirstL, tr1, hrun1, hq1⟩ := run_choose_ex V o N.toList hnil s []
    have hfirst : first ∈ N := Finset.mem_toList.mp hfirstL
    have hnil2 : N.toList.erase first ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [List.length_erase_of_mem hfirstL, Finset.length_toList, h2] at this
      simp at this
    obtain ⟨second, hsecL, tr2, hrun2, hq2⟩ := run_choose_ex V o _ hnil2 s tr1
    obtain ⟨hsf, hsecL'⟩ := (Finset.nodup_toList N).mem_erase_iff.mp hsecL
    have hsecond : second ∈ N := Finset.mem_toList.mp hsecL'
    have hNpair : ∀ j ∈ N, j = first ∨ j = second := by
      intro j hj
      by_contra hcon
      push Not at hcon
      have hsub : ({j, first, second} : Finset ι) ⊆ N := by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl <;> assumption
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp [hcon.1, hcon.2]),
        Finset.card_insert_of_notMem (by simpa using hsf.symm), Finset.card_singleton] at this
      omega
    have hvC := recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
      V N s hs first hfirst C hC hCs
    set w := s.pieceVal first C / 2 with hw
    have hC0 : 0 ≤ (V first).value C.toSet := value_nonneg _ (hmeas C)
    obtain ⟨p, s1, tr3, hpc, hs1, hsub1, hP0wf, hP1wf, hP0al, hP1al, hv0, hv1, -, -⟩ :=
      prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2 V N first hfirst C
        hC s hs hCs w (by rw [hw, hvC]; linarith) (by rw [hw, hvC]; linarith) o tr2
    obtain ⟨p', s1', tr3', hpc', -, -, hvp, -⟩ :=
      prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1 V N first hfirst C
        hC s hs hCs w (by rw [hw, hvC]; linarith) (by rw [hw, hvC]; linarith) o tr2
    rw [hpc] at hpc'
    simp only [Option.some.injEq, Prod.mk.injEq] at hpc'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hpc'
    have hq3 := prefixCut_query_bound__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1
      V N first C w s o tr2 p s1 tr3 hpc
    set P0 := prefixList C p
    set P1 := suffixList C p
    have hpart : Disjoint P0.toSet P1.toSet ∧ P0.toSet ∪ P1.toSet = C.toSet := by
      rcases hvp with rfl | hvp
      · simp [P0, P1, prefixList, suffixList, toSet_nil]
      · exact (cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1 C hC p hvp).2.2
    have hrec : ∀ i ∈ N, ∀ P : Piece, P.WF → s1.Aligned P → s1.pieceVal i P = (V i).value P.toSet :=
      fun i hi P hP hPa =>
        recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1 V N s1 hs1 i hi P hP hPa
    let halves : List Piece := [P0, P1]
    let L := [0, 1].filter (fun k => decide (∀ k' ∈ [0, 1],
      s1.pieceVal second (halves.getD k' []) ≤ s1.pieceVal second (halves.getD k [])))
    have hLne : L ≠ [] := by
      rcases le_total (s1.pieceVal second P0) (s1.pieceVal second P1) with h | h
      · intro hL
        have : (1 : ℕ) ∈ L := by
          simp only [L, List.mem_filter, decide_eq_true_eq]
          refine ⟨by simp, ?_⟩
          intro k' hk'; simp at hk'; rcases hk' with rfl | rfl <;> simp [halves, h]
        rw [hL] at this; simp at this
      · intro hL
        have : (0 : ℕ) ∈ L := by
          simp only [L, List.mem_filter, decide_eq_true_eq]
          refine ⟨by simp, ?_⟩
          intro k' hk'; simp at hk'; rcases hk' with rfl | rfl <;> simp [halves, h]
        rw [hL] at this; simp at this
    obtain ⟨k, hkL, tr4, hrun4, hq4⟩ := run_choose_ex V o L hLne s1 tr3
    obtain ⟨hk01, hkmax⟩ := List.mem_filter.mp hkL
    simp only [decide_eq_true_eq] at hkmax
    let A : ι → Piece := fun j => if j = second then halves.getD k []
      else if j = first then halves.getD (1 - k) [] else []
    refine ⟨1, A, s1, tr4, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [exec_iff, divide, if_neg h1, if_pos h2, run_stbind, hrun1]
      dsimp only
      rw [run_stbind, hrun2]; dsimp only
      rw [run_stbind, run_get']; dsimp only
      rw [run_stbind, hpc]; dsimp only
      rw [run_stbind, run_get']; dsimp only
      rw [run_stbind, hrun4]; rfl
    · have hP0C : P0.toSet ⊆ C.toSet := hpart.2 ▸ Set.subset_union_left
      have hP1C : P1.toSet ⊆ C.toSet := hpart.2 ▸ Set.subset_union_right
      intro i _
      simp only [A]
      split_ifs <;> simp at hk01 <;> rcases hk01 with rfl | rfl <;>
        simp [halves, hP0C, hP1C, toSet_nil]
    · intro i hi j hj hij
      rcases hNpair i hi with rfl | rfl <;> rcases hNpair j hj with rfl | rfl
      · exact absurd rfl hij
      · simp only [A, if_pos rfl, if_neg hsf.symm]
        simp at hk01; rcases hk01 with rfl | rfl
        · simpa [halves] using hpart.1.symm
        · simpa [halves] using hpart.1
      · simp only [A, if_pos rfl, if_neg hsf.symm]
        simp at hk01; rcases hk01 with rfl | rfl
        · simpa [halves] using hpart.1
        · simpa [halves] using hpart.1.symm
      · exact absurd rfl hij
    · unfold EnvyFreeCake104.Divide.IsComplete
      rw [← hpart.2]
      ext y
      simp only [Set.mem_iUnion, exists_prop, Set.mem_union]
      constructor
      · rintro ⟨j, hj, hy⟩
        simp only [A] at hy
        split_ifs at hy <;> simp at hk01 <;> rcases hk01 with rfl | rfl <;>
          simp [halves, toSet_nil] at hy <;> tauto
      · have hfA : A first = halves.getD (1 - k) [] := by simp [A, hsf.symm]
        have hsA : A second = halves.getD k [] := by simp [A]
        simp at hk01
        rintro (hy | hy)
        · rcases hk01 with rfl | rfl
          · exact ⟨second, hsecond, by rw [hsA]; simpa [halves] using hy⟩
          · exact ⟨first, hfirst, by rw [hfA]; simpa [halves] using hy⟩
        · rcases hk01 with rfl | rfl
          · exact ⟨first, hfirst, by rw [hfA]; simpa [halves] using hy⟩
          · exact ⟨second, hsecond, by rw [hsA]; simpa [halves] using hy⟩
    · have hfA : A first = halves.getD (1 - k) [] := by simp [A, hsf.symm]
      have hsA : A second = halves.getD k [] := by simp [A]
      have hk01' : k = 0 ∨ k = 1 := by simpa using hk01
      have hval1 : (V first).value P1.toSet = (V first).value C.toSet / 2 := by
        rw [hv1, hw, hvC]; ring
      have hval0 : (V first).value P0.toSet = (V first).value C.toSet / 2 := by
        rw [hv0, hw, hvC]
      intro i hi j hj
      rcases hNpair i hi with rfl | rfl <;> rcases hNpair j hj with rfl | rfl
      · exact le_rfl
      · show (V i).value (A j).toSet ≤ (V i).value (A i).toSet
        rw [hfA, hsA]
        rcases hk01' with rfl | rfl <;> simp [halves, hval0, hval1]
      · show (V i).value (A j).toSet ≤ (V i).value (A i).toSet
        rw [hfA, hsA]
        have := hkmax (1 - k) (by rcases hk01' with rfl | rfl <;> simp)
        rcases hk01' with rfl | rfl
        · simp only [halves] at this ⊢
          simpa [hrec i hsecond P0 hP0wf hP0al, hrec i hsecond P1 hP1wf hP1al] using this
        · simp only [halves] at this ⊢
          simpa [hrec i hsecond P0 hP0wf hP0al, hrec i hsecond P1 hP1wf hP1al] using this
      · exact le_rfl
    · rw [hq4, h2]
      have : queryCount tr2 = 0 := by rw [hq2, hq1]; rfl
      rw [h2] at hq3
      have hB : 3 ≤ 2 * B 2 := by unfold B; norm_num
      omega
  -- three or more agents
  have h3 : 3 ≤ N.card := by
    have := Finset.card_pos.mpr hNne; omega
  obtain ⟨f1, X, R, E, s1, tr1, hex1, hpa, hres, hEFX, hdom, hq1⟩ :=
    EnvyFreeCake104.Divide.lemma_1 V N h3 C hC s hs hCs o
  have hrun1 := (exec_iff V o _ s _ s1 tr1).mp hex1
  obtain ⟨hs1, hRwf, hRal⟩ :=
    EnvyFreeCake104.Divide.dominate_invariants V N h3 C hC s hs hCs f1 o [] X R E s1 tr1 hrun1
  obtain ⟨hEN, hEne, hENe, hdomE⟩ := hdom
  have hEcard : E.card < N.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hEN, hENe⟩)
  obtain ⟨f2, Y, s2, tc, hex2, hpaY, hcompY, hEFY, hq2⟩ :=
    ih E.card (hNn ▸ hEcard) E rfl hEne R hRwf s1 (valid_mono V N E s1 hs1 hEN) hRal
      (fun t m ↦ o (tr1 ++ t) m)
  have hrun2 := run_from_exec V o _ s1 tr1 Y s2 tc hex2
  set F := max f1 f2
  have hrun1F := dominate_mono V N C f1 F (le_max_left _ _) s o [] _ hrun1
  have hrun2F := divide_mono V f2 F (le_max_right _ _) E R s1 o tr1 _ hrun2
  let Ys : ι → Set ℝ := fun i => if i ∈ E then (Y i).toSet else ∅
  let A : ι → Piece := fun i => if i ∈ N then X i ++ (if i ∈ E then Y i else []) else []
  have hA : ∀ i ∈ N, (A i).toSet = (X i).toSet ∪ Ys i := by
    intro i hi
    simp only [A, Ys, if_pos hi, toSet_append]
    split_ifs <;> simp [toSet_nil]
  have hmYs : ∀ i, MeasurableSet (Ys i) := by
    intro i; simp only [Ys]; split_ifs
    · exact hmeas _
    · exact MeasurableSet.empty
  have hYsR : ∀ i, Ys i ⊆ R.toSet := by
    intro i; simp only [Ys]; split_ifs with h
    · exact hpaY.1 i h
    · exact Set.empty_subset _
  have hXU : ∀ i ∈ N, (X i).toSet ⊆ ⋃ j ∈ N, (X j).toSet :=
    fun i hi => Set.subset_biUnion_of_mem (u := fun j => (X j).toSet) hi
  have hXR : ∀ i ∈ N, Disjoint (X i).toSet R.toSet := by
    intro i hi
    rw [hres]; unfold residue
    exact Disjoint.mono_left (hXU i hi) Set.disjoint_sdiff_right
  have hXYs : ∀ i ∈ N, ∀ j, Disjoint (X i).toSet (Ys j) :=
    fun i hi j => Disjoint.mono_right (hYsR j) (hXR i hi)
  have hvA : ∀ k, ∀ i ∈ N, (V k).value (A i).toSet = (V k).value (X i).toSet + (V k).value (Ys i) :=
    fun k i hi => by rw [hA i hi, value_union _ (hmYs i) (hXYs i hi i)]
  refine ⟨F + 1, A, s2, tr1 ++ tc, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [exec_iff, divide, if_neg h1, if_neg h2, if_neg (by omega), run_stbind, hrun1F]
    dsimp only
    rw [run_stbind, hrun2F]; rfl
  · intro i hi
    beta_reduce
    rw [hA i hi]
    refine Set.union_subset (hpa.1 i hi) ((hYsR i).trans ?_)
    rw [hres]; exact Set.sdiff_subset
  · intro i hi j hj hij
    beta_reduce
    rw [hA i hi, hA j hj]
    refine Disjoint.union_left (Disjoint.union_right (hpa.2 i hi j hj hij) (hXYs i hi j))
      (Disjoint.union_right (hXYs j hj i).symm ?_)
    simp only [Ys]; split_ifs with hiE hjE
    · exact hpaY.2 i hiE j hjE hij
    · exact Set.disjoint_empty _
    · exact Set.empty_disjoint _
    · exact Set.empty_disjoint _
  · unfold EnvyFreeCake104.Divide.IsComplete
    have hRC : R.toSet = C.toSet \ ⋃ j ∈ N, (X j).toSet := by rw [hres]; rfl
    have hXC : (⋃ j ∈ N, (X j).toSet) ⊆ C.toSet := Set.iUnion₂_subset hpa.1
    ext y
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨i, hi, hy⟩
      rw [hA i hi] at hy
      rcases hy with hy | hy
      · exact hpa.1 i hi hy
      · have := hYsR i hy; rw [hRC] at this; exact this.1
    · intro hy
      by_cases hyX : y ∈ ⋃ j ∈ N, (X j).toSet
      · simp only [Set.mem_iUnion, exists_prop] at hyX
        obtain ⟨i, hi, hyi⟩ := hyX
        exact ⟨i, hi, by rw [hA i hi]; exact Or.inl hyi⟩
      · have hyR : y ∈ R.toSet := by rw [hRC]; exact ⟨hy, hyX⟩
        rw [← hcompY] at hyR
        simp only [Set.mem_iUnion, exists_prop] at hyR
        obtain ⟨i, hiE, hyi⟩ := hyR
        exact ⟨i, hEN hiE, by rw [hA i (hEN hiE)]; right; simp only [Ys, if_pos hiE]; exact hyi⟩
  · intro i hi j hj
    show (V i).value (A j).toSet ≤ (V i).value (A i).toSet
    rw [hvA i j hj, hvA i i hi]
    have hX := hEFX i hi j hj
    have hYs0 : 0 ≤ (V i).value (Ys i) := value_nonneg _ (hmYs i)
    by_cases hiE : i ∈ E
    · by_cases hjE : j ∈ E
      · have := hEFY i hiE j hjE
        simp only [Ys, if_pos hiE, if_pos hjE]
        linarith
      · simp only [Ys, if_neg hjE, value_empty]; linarith
    · by_cases hjE : j ∈ E
      · have hdij := hdomE i hi hiE j hjE
        unfold Dominates at hdij
        have := value_mono (V i) (hYsR j) (hmeas R)
        simp only [Ys, if_neg hiE, if_pos hjE, value_empty] at *
        linarith
      · simp only [Ys, if_neg hiE, if_neg hjE, value_empty]; linarith
  · rw [queryCount, List.countP_append]
    have hq1' : queryCount tr1 ≤ B N.card := hq1
    have hBE : B E.card ≤ B (N.card - 1) := B_mono (by omega)
    have hBN : 32 * B (N.card - 1) ≤ B N.card := by
      have := B_succ (N.card - 1); rwa [Nat.sub_add_cancel (by omega)] at this
    unfold queryCount at hq1' hq2
    omega


theorem nat_bound (m : ℕ) (hm : 2 ≤ m) : 2 * 32 ^ m * m ^ 7 * (m.factorial) ^ 2 ≤ m ^ (15 * m) := by
  have h1 : 2 ≤ m ^ m := le_trans hm (Nat.le_self_pow (by omega) m)
  have h2 : 32 ^ m ≤ m ^ (5 * m) := by
    rw [pow_mul]
    apply Nat.pow_le_pow_left
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ m ^ 5 := Nat.pow_le_pow_left hm 5
  have h3 : m ^ 7 ≤ m ^ (7 * m) := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : m.factorial ^ 2 ≤ m ^ (2 * m) := by
    rw [mul_comm 2 m, pow_mul]; exact Nat.pow_le_pow_left (Nat.factorial_le_pow m) 2
  calc 2 * 32 ^ m * m ^ 7 * m.factorial ^ 2
      ≤ m ^ m * m ^ (5 * m) * m ^ (7 * m) * m ^ (2 * m) := by
        apply Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3) h4
    _ = m ^ (15 * m) := by rw [← pow_add, ← pow_add, ← pow_add]; ring_nf

theorem part3 : ∃ c : ℝ, ∀ m : ℕ, 2 ≤ m →
    ((2 * 32 ^ m * m ^ 7 * (m.factorial) ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (c * m * Real.logb 2 m) := by
  refine ⟨15, fun m hm => ?_⟩
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnat := nat_bound m hm
  have hcast : ((2 * 32 ^ m * m ^ 7 * (m.factorial) ^ 2 : ℕ) : ℝ) ≤ ((m : ℝ)) ^ (15 * m) := by
    exact_mod_cast hnat
  refine hcast.trans (le_of_eq ?_)
  have hlog : (2 : ℝ) ^ Real.logb 2 m = m :=
    Real.rpow_logb (by norm_num) (by norm_num) hmpos
  conv_lhs => rw [← hlog]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  push_cast; ring

theorem initRec_valid (n : ℕ) (V : Fin n → Valuation)
    (hV : ∀ i, (V i).value (Set.Icc 0 1) = 1) : (initRec (Fin n)).Valid V Finset.univ := by
  refine ⟨by simp [initRec], by simp [initRec], ?_, ?_⟩
  · intro c hc; simp [initRec] at hc; rcases hc with rfl | rfl <;> norm_num
  · intro i _ c hc hc1
    simp [initRec] at hc
    rcases hc with rfl | rfl
    · have hnext : (initRec (Fin n)).nextPt 0 = 1 := by
        unfold Rec.nextPt
        have hne : ((initRec (Fin n)).pts.filter (fun d => (0:ℝ) < d)).Nonempty :=
          ⟨1, by simp [initRec]⟩
        rw [dif_pos hne]
        apply le_antisymm
        · exact Finset.min'_le _ _ (by simp [initRec])
        · apply Finset.le_min'
          intro y hy
          simp only [initRec, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with ⟨rfl | rfl, h⟩
          · exact absurd h (lt_irrefl 0)
          · exact le_rfl
      rw [hnext]
      simp only [initRec, if_true]
      have hIco : (V i).value (Set.Ico 0 1) = (V i).value (Set.Icc 0 1) := by
        unfold Valuation.value
        rw [Set.inter_eq_left.mpr Set.Ico_subset_Icc_self, Set.inter_self]
        exact MeasureTheory.integral_Icc_eq_integral_Ico.symm
      rw [hIco, hV i]
    · norm_num at hc1

open scoped Classical in
theorem part2 : ∀ (n : ℕ), 1 ≤ n → ∀ (V : Fin n → Valuation), (∀ i, (V i).value (Set.Icc 0 1) = 1) →
      ∀ o : ChoiceOracle (Fin n),
      ∃ (fuel : ℕ) (A : Fin n → Piece) (tr : List (Event (Fin n))),
        runDivide V o fuel = some (A, tr) ∧
        IsPartialAlloc Finset.univ (Set.Icc 0 1) (fun i => (A i).toSet) ∧
        EnvyFreeCake104.Divide.IsComplete Finset.univ (Set.Icc 0 1) (fun i => (A i).toSet) ∧
        EnvyFree V Finset.univ (fun i => (A i).toSet) ∧
        queryCount tr ≤ 2 * 32 ^ n * n ^ 7 * (n.factorial) ^ 2 := by
  intro n hn V hV o
  have hC : Piece.WF [⟨0, 1⟩] := ⟨by simp, by simp⟩
  have hCset : Piece.toSet [⟨(0:ℝ), 1⟩] = Set.Icc 0 1 := by
    ext x; simp [Piece.toSet, Interval.toSet]
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨fuel, A, s', tr, hex, hpa, hcomp, hEF, hq⟩ :=
    part1 V _ Finset.univ rfl hne [⟨0, 1⟩] hC (initRec (Fin n)) (initRec_valid n V hV)
      (fun I hI => by simp at hI; subst hI; simp [initRec]) o
  rw [hCset] at hpa hcomp
  refine ⟨fuel, A, tr, ?_, hpa, hcomp, hEF, ?_⟩
  · unfold runDivide; rw [hex]
  · simp only [B, Finset.card_univ, Fintype.card_fin] at hq
    calc queryCount tr ≤ 2 * (32 ^ n * n ^ 7 * n.factorial ^ 2) := hq
      _ = 2 * 32 ^ n * n ^ 7 * n.factorial ^ 2 := by ring

end T2Aux

open T2Aux in
open scoped Classical in
theorem solution :
    (∀ {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι), N.Nonempty →
      ∀ C : Piece, C.WF → ∀ s : Rec ι, s.Valid V N → s.Aligned C → ∀ o : ChoiceOracle ι,
      ∃ (fuel : ℕ) (A : ι → Piece) (s' : Rec ι) (tr : List (Event ι)),
        exec V o (divide fuel N C) s = some (A, s', tr) ∧
        IsPartialAlloc N C.toSet (fun i => (A i).toSet) ∧
        EnvyFreeCake104.Divide.IsComplete N C.toSet (fun i => (A i).toSet) ∧
        EnvyFree V N (fun i => (A i).toSet) ∧
        queryCount tr ≤ 2 * 32 ^ N.card * N.card ^ 7 * (N.card.factorial) ^ 2) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (V : Fin n → Valuation), (∀ i, (V i).value (Set.Icc 0 1) = 1) →
      ∀ o : ChoiceOracle (Fin n),
      ∃ (fuel : ℕ) (A : Fin n → Piece) (tr : List (Event (Fin n))),
        runDivide V o fuel = some (A, tr) ∧
        IsPartialAlloc Finset.univ (Set.Icc 0 1) (fun i => (A i).toSet) ∧
        EnvyFreeCake104.Divide.IsComplete Finset.univ (Set.Icc 0 1) (fun i => (A i).toSet) ∧
        EnvyFree V Finset.univ (fun i => (A i).toSet) ∧
        queryCount tr ≤ 2 * 32 ^ n * n ^ 7 * (n.factorial) ^ 2) ∧
    (∃ c : ℝ, ∀ m : ℕ, 2 ≤ m →
      ((2 * 32 ^ m * m ^ 7 * (m.factorial) ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (c * m * Real.logb 2 m)) := by
  refine ⟨?_, part2, part3⟩
  intro ι _ V N hNne C hC s hs hCs o
  obtain ⟨fuel, A, s', tr, hex, hpa, hcomp, hEF, hq⟩ := part1 V _ N rfl hNne C hC s hs hCs o
  refine ⟨fuel, A, s', tr, hex, hpa, hcomp, hEF, ?_⟩
  calc queryCount tr ≤ 2 * B N.card := hq
    _ = 2 * 32 ^ N.card * N.card ^ 7 * (N.card.factorial) ^ 2 := by unfold B; ring
