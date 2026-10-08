-- Prove2me | solution 1 for FlowJobShop.PartitionFlow.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:39:05.3983+00:00
-- url     : https://prove2.me/submissions/507f0238-f5f7-4f63-9a99-bb828e1af430

import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionFlow_Instance

open FlowJobShop.PartitionFlow.FlowShop


namespace FlowJobShop.PartitionFlow

open MeasureTheory

theorem cap_gen {α : Type*} (s : Finset α) (lo hi : α → ℝ)
    (hd : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → hi x ≤ lo y ∨ hi y ≤ lo x) (a b : ℝ) (hab : a ≤ b) :
    ∑ x ∈ s, max 0 (min (hi x) b - max (lo x) a) ≤ b - a := by
  classical
  have h1 : ∀ x, ENNReal.ofReal (max 0 (min (hi x) b - max (lo x) a)) =
      volume (Set.Ico (max (lo x) a) (min (hi x) b)) := by
    intro x
    rw [Real.volume_Ico]
    by_cases h : 0 ≤ min (hi x) b - max (lo x) a
    · rw [max_eq_right h]
    · rw [max_eq_left (le_of_not_ge h), ENNReal.ofReal_of_nonpos (le_of_not_ge h)]
      simp
  have hdisj : Set.PairwiseDisjoint (↑s : Set α)
      (fun x => Set.Ico (max (lo x) a) (min (hi x) b)) := by
    intro x hx y hy hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hz1 hz2
    rcases hd x hx y hy hxy with h | h
    · have := hz1.2; have := hz2.1
      have := min_le_left (hi x) b; have := le_max_left (lo y) a
      linarith
    · have := hz2.2; have := hz1.1
      have := min_le_left (hi y) b; have := le_max_left (lo x) a
      linarith
  have h2 : ∑ x ∈ s, ENNReal.ofReal (max 0 (min (hi x) b - max (lo x) a)) ≤ ENNReal.ofReal (b - a) := by
    calc _ = ∑ x ∈ s, volume (Set.Ico (max (lo x) a) (min (hi x) b)) := Finset.sum_congr rfl (fun x _ => h1 x)
      _ = volume (⋃ x ∈ s, Set.Ico (max (lo x) a) (min (hi x) b)) :=
          (measure_biUnion_finset hdisj (fun _ _ => measurableSet_Ico)).symm
      _ ≤ volume (Set.Ico a b) := measure_mono (Set.iUnion₂_subset fun x _ =>
          Set.Ico_subset_Ico (le_max_right _ _) (min_le_right _ _))
      _ = ENNReal.ofReal (b - a) := Real.volume_Ico
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => le_max_left _ _)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h2

/-- overlap of a piece with window [a,b] -/
noncomputable def ov (p : ℝ × ℝ) (a b : ℝ) : ℝ := max 0 (min p.2 b - max p.1 a)

theorem ov_nonneg (p : ℝ × ℝ) (a b : ℝ) : 0 ≤ ov p a b := le_max_left _ _

theorem ov_of_sub {p : ℝ × ℝ} {a b : ℝ} (h1 : a ≤ p.1) (h2 : p.2 ≤ b) (h : p.1 ≤ p.2) :
    ov p a b = p.2 - p.1 := by
  unfold ov
  rw [min_eq_left h2, max_eq_left h1]
  exact max_eq_right (by linarith)

theorem ov_split {p : ℝ × ℝ} {T : ℝ} (hT : 0 ≤ T) (h0 : 0 ≤ p.1) (h : p.1 ≤ p.2) (h2 : p.2 ≤ 2 * T) :
    ov p 0 T + ov p T (2 * T) = p.2 - p.1 := by
  unfold ov
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem piece_end_le {m : ℕ} {J : Type*} [Fintype J] {F : FlowShop m J} (S : PreemptiveSchedule F)
    (j : Fin m) (i : J) (p : ℝ × ℝ) (hp : p ∈ S.pieces j i) : p.2 ≤ S.finishTime := by
  unfold PreemptiveSchedule.finishTime
  rw [Finset.le_fold_max]
  right
  refine ⟨i, Finset.mem_univ _, ?_⟩
  unfold PreemptiveSchedule.jobFinish
  rw [Finset.le_fold_max]
  right
  exact ⟨p, Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hp⟩, le_rfl⟩

theorem cap_task {m : ℕ} {J : Type*} {F : FlowShop m J} (S : PreemptiveSchedule F)
    (j : Fin m) (i : J) (a b : ℝ) (hab : a ≤ b) :
    ∑ p ∈ S.pieces j i, ov p a b ≤ b - a := by
  apply cap_gen (S.pieces j i) (fun p => p.1) (fun p => p.2) _ a b hab
  intro x hx y hy hxy
  exact S.disjoint j i i x y hx hy (by simpa using hxy)

theorem cap_proc {m : ℕ} {J : Type*} [Fintype J] {F : FlowShop m J} (S : PreemptiveSchedule F)
    (j : Fin m) (a b : ℝ) (hab : a ≤ b) :
    ∑ i, ∑ p ∈ S.pieces j i, ov p a b ≤ b - a := by
  classical
  rw [← Finset.sum_sigma (Finset.univ : Finset J) (fun i => S.pieces j i)
    (fun x => ov x.2 a b)]
  refine cap_gen (Finset.univ.sigma (fun i => S.pieces j i)) (fun x => x.2.1) (fun x => x.2.2) ?_ a b hab
  intro x hx y hy hxy
  rw [Finset.mem_sigma] at hx hy
  apply S.disjoint j x.1 y.1 x.2 y.2 hx.2 hy.2
  intro h
  apply hxy
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem observations_core {n : ℕ} (a : Fin n → ℕ) (S : PreemptiveSchedule (FS a))
    (hS : S.finishTime ≤ 2 * T a) :
    (∀ p ∈ S.pieces 0 (Sum.inr 0), p.2 ≤ T a) ∧
      (∀ p ∈ S.pieces 2 (Sum.inr 1), T a ≤ p.1) := by
  have hend : ∀ j i, ∀ p ∈ S.pieces j i, p.2 ≤ 2 * T a :=
    fun j i p hp => (piece_end_le S j i p hp).trans hS
  constructor
  · intro p hp
    by_contra hlt
    push Not at hlt
    have hsum := S.total_length 1 (Sum.inr 0)
    have ht : (FS a).t 1 (Sum.inr 0) = T a := by simp [FS, fsTimes]
    rw [ht] at hsum
    have hcap := cap_task S 1 (Sum.inr 0) p.2 (2 * T a) (hend 0 _ p hp)
    have : ∑ q ∈ S.pieces 1 (Sum.inr 0), ov q p.2 (2 * T a)
        = ∑ q ∈ S.pieces 1 (Sum.inr 0), (q.2 - q.1) :=
      Finset.sum_congr rfl (fun q hq => ov_of_sub
        (S.precedence (Sum.inr 0) 0 1 (by decide) p hp q hq) (hend 1 _ q hq)
        (S.start_lt_end 1 _ q hq).le)
    linarith
  · intro p hp
    by_contra hlt
    push Not at hlt
    have hsum := S.total_length 1 (Sum.inr 1)
    have ht : (FS a).t 1 (Sum.inr 1) = T a := by simp [FS, fsTimes]
    rw [ht] at hsum
    have hcap := cap_task S 1 (Sum.inr 1) 0 p.1 (S.start_nonneg 2 _ p hp)
    have : ∑ q ∈ S.pieces 1 (Sum.inr 1), ov q 0 p.1
        = ∑ q ∈ S.pieces 1 (Sum.inr 1), (q.2 - q.1) :=
      Finset.sum_congr rfl (fun q hq => ov_of_sub
        (S.start_nonneg 1 _ q hq) (S.precedence (Sum.inr 1) 1 2 (by decide) q hq p hp)
        (S.start_lt_end 1 _ q hq).le)
    linarith


theorem lemma_1b_core {n : ℕ} (a : Fin n → ℕ) (h : ¬ HasPartition a) :
    ∀ S : PreemptiveSchedule (FS a), 2 * T a < S.finishTime := by
  classical
  intro S
  by_contra hle
  push Not at hle
  obtain ⟨o1, o2⟩ := observations_core a S hle
  have hend : ∀ j i, ∀ p ∈ S.pieces j i, p.2 ≤ 2 * T a :=
    fun j i p hp => (piece_end_le S j i p hp).trans hle
  have hT := T_nonneg a
  -- P1 capacity
  have P1cap : ∑ i : Fin n, ∑ p ∈ S.pieces 0 (Sum.inl i), ov p 0 (T a) ≤ T a / 2 := by
    have hc := cap_proc S 0 0 (T a) hT
    rw [Fintype.sum_sum_type, Fin.sum_univ_two] at hc
    have e : ∑ p ∈ S.pieces 0 (Sum.inr 0), ov p 0 (T a) = T a / 2 := by
      have := S.total_length 0 (Sum.inr 0)
      have ht : (FS a).t 0 (Sum.inr 0) = T a / 2 := by simp [FS, fsTimes]
      rw [ht] at this
      rw [← this]
      exact Finset.sum_congr rfl (fun q hq => ov_of_sub (S.start_nonneg 0 _ q hq) (o1 q hq)
        (S.start_lt_end 0 _ q hq).le)
    have e2 : 0 ≤ ∑ p ∈ S.pieces 0 (Sum.inr 1), ov p 0 (T a) :=
      Finset.sum_nonneg (fun p _ => ov_nonneg _ _ _)
    linarith
  -- P3 capacity
  have P3cap : ∑ i : Fin n, ∑ p ∈ S.pieces 2 (Sum.inl i), ov p (T a) (2 * T a) ≤ T a / 2 := by
    have hc := cap_proc S 2 (T a) (2 * T a) (by linarith)
    rw [Fintype.sum_sum_type, Fin.sum_univ_two] at hc
    have e : ∑ p ∈ S.pieces 2 (Sum.inr 1), ov p (T a) (2 * T a) = T a / 2 := by
      have := S.total_length 2 (Sum.inr 1)
      have ht : (FS a).t 2 (Sum.inr 1) = T a / 2 := by simp [FS, fsTimes]
      rw [ht] at this
      rw [← this]
      exact Finset.sum_congr rfl (fun q hq => ov_of_sub (o2 q hq) (hend 2 _ q hq)
        (S.start_lt_end 2 _ q hq).le)
    have e2 : 0 ≤ ∑ p ∈ S.pieces 2 (Sum.inr 0), ov p (T a) (2 * T a) :=
      Finset.sum_nonneg (fun p _ => ov_nonneg _ _ _)
    linarith
  -- split of P3 tasks of jobs
  have split3 : ∀ i : Fin n, ∑ p ∈ S.pieces 2 (Sum.inl i), ov p 0 (T a)
      + ∑ p ∈ S.pieces 2 (Sum.inl i), ov p (T a) (2 * T a) = (a i : ℝ) := by
    intro i
    rw [← Finset.sum_add_distrib]
    have := S.total_length 2 (Sum.inl i)
    have ht : (FS a).t 2 (Sum.inl i) = (a i : ℝ) := by simp [FS, fsTimes]
    rw [ht] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun q hq => ov_split hT (S.start_nonneg 2 _ q hq)
      (S.start_lt_end 2 _ q hq).le (hend 2 _ q hq))
  set u : Finset (Fin n) := Finset.univ.filter
    (fun i => ∃ p ∈ S.pieces 2 (Sum.inl i), p.1 < T a) with hu
  have hTsum : T a = ∑ i, (a i : ℝ) := rfl
  have P3low : T a / 2 ≤ ∑ i : Fin n, ∑ p ∈ S.pieces 2 (Sum.inl i), ov p 0 (T a) := by
    have : ∑ i : Fin n, ((∑ p ∈ S.pieces 2 (Sum.inl i), ov p 0 (T a))
      + ∑ p ∈ S.pieces 2 (Sum.inl i), ov p (T a) (2 * T a)) = T a := by
      rw [hTsum]; exact Finset.sum_congr rfl (fun i _ => split3 i)
    rw [Finset.sum_add_distrib] at this
    linarith
  have P3u : ∑ i : Fin n, ∑ p ∈ S.pieces 2 (Sum.inl i), ov p 0 (T a)
      ≤ ∑ i ∈ u, (a i : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ u)]
    have hf : Finset.univ.filter (fun i => i ∈ u) = u := by ext; simp
    rw [hf]
    have z : ∑ i ∈ Finset.univ.filter (fun i => i ∉ u), ∑ p ∈ S.pieces 2 (Sum.inl i), ov p 0 (T a) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hiu : i ∉ u := by simpa using hi
      apply Finset.sum_eq_zero
      intro p hp
      have : T a ≤ p.1 := by
        by_contra hlt
        push Not at hlt
        exact hiu (by simp only [hu, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨p, hp, hlt⟩)
      unfold ov
      apply max_eq_left
      have := min_le_right p.2 (T a)
      have := le_max_left p.1 0
      linarith
    rw [z, add_zero]
    apply Finset.sum_le_sum
    intro i _
    have := split3 i
    have e2 : 0 ≤ ∑ p ∈ S.pieces 2 (Sum.inl i), ov p (T a) (2 * T a) :=
      Finset.sum_nonneg (fun p _ => ov_nonneg _ _ _)
    linarith
  have P1u : ∀ i ∈ u, ∑ p ∈ S.pieces 0 (Sum.inl i), ov p 0 (T a) = (a i : ℝ) := by
    intro i hi
    simp only [hu, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨p, hp, hp1⟩ := hi
    have := S.total_length 0 (Sum.inl i)
    have ht : (FS a).t 0 (Sum.inl i) = (a i : ℝ) := by simp [FS, fsTimes]
    rw [ht] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun q hq => ov_of_sub (S.start_nonneg 0 _ q hq)
      (by have := S.precedence (Sum.inl i) 0 2 (by decide) q hq p hp; linarith)
      (S.start_lt_end 0 _ q hq).le)
  have P1le : ∑ i ∈ u, (a i : ℝ) ≤ T a / 2 := by
    calc ∑ i ∈ u, (a i : ℝ) = ∑ i ∈ u, ∑ p ∈ S.pieces 0 (Sum.inl i), ov p 0 (T a) :=
          (Finset.sum_congr rfl (fun i hi => (P1u i hi).symm))
      _ ≤ ∑ i : Fin n, ∑ p ∈ S.pieces 0 (Sum.inl i), ov p 0 (T a) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => Finset.sum_nonneg (fun p _ => ov_nonneg _ _ _))
      _ ≤ T a / 2 := P1cap
  apply h
  refine ⟨u, ?_⟩
  have h2 : 2 * ∑ i ∈ u, (a i : ℝ) = ∑ i, (a i : ℝ) := by
    rw [← hTsum]; linarith
  exact_mod_cast h2


section Builder

theorem mem_pc {t s : ℝ} {p : ℝ × ℝ} :
    p ∈ (if t = 0 then (∅ : Finset (ℝ × ℝ)) else {(s, s + t)}) ↔ t ≠ 0 ∧ p = (s, s + t) := by
  by_cases h : t = 0 <;> simp [h]

noncomputable def mkSched {m : ℕ} {J : Type*} (F : FlowShop m J) (st : Fin m → J → ℝ)
    (hnn : ∀ j i, F.t j i ≠ 0 → 0 ≤ st j i)
    (hsep : ∀ j i i', i ≠ i' → F.t j i = 0 ∨ F.t j i' = 0 ∨
      st j i + F.t j i ≤ st j i' ∨ st j i' + F.t j i' ≤ st j i)
    (hprec : ∀ i j j', j < j' → F.t j i = 0 ∨ F.t j' i = 0 ∨ st j i + F.t j i ≤ st j' i) :
    PreemptiveSchedule F where
  pieces j i := if F.t j i = 0 then ∅ else {(st j i, st j i + F.t j i)}
  start_nonneg := by
    intro j i p hp
    obtain ⟨h1, rfl⟩ := mem_pc.1 hp
    exact hnn j i h1
  start_lt_end := by
    intro j i p hp
    obtain ⟨h1, rfl⟩ := mem_pc.1 hp
    have := F.t_nonneg j i
    show st j i < st j i + F.t j i
    have : 0 < F.t j i := lt_of_le_of_ne this (Ne.symm h1)
    linarith
  disjoint := by
    intro j i i' p p' hp hp' hne
    obtain ⟨h1, rfl⟩ := mem_pc.1 hp
    obtain ⟨h2, rfl⟩ := mem_pc.1 hp'
    by_cases hii : i = i'
    · subst hii; exact absurd rfl hne
    · rcases hsep j i i' hii with h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact Or.inl h
      · exact Or.inr h
  total_length := by
    intro j i
    by_cases h : F.t j i = 0
    · simp [h]
    · simp [h]
  precedence := by
    intro i j j' hjj p hp p' hp'
    obtain ⟨h1, rfl⟩ := mem_pc.1 hp
    obtain ⟨h2, rfl⟩ := mem_pc.1 hp'
    rcases hprec i j j' hjj with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h

theorem mkSched_pieces {m : ℕ} {J : Type*} (F : FlowShop m J) (st : Fin m → J → ℝ) hnn hsep hprec
    (j : Fin m) (i : J) :
    (mkSched F st hnn hsep hprec).pieces j i =
      if F.t j i = 0 then ∅ else {(st j i, st j i + F.t j i)} := rfl

theorem mkSched_nonpre {m : ℕ} {J : Type*} (F : FlowShop m J) (st : Fin m → J → ℝ) hnn hsep hprec :
    (mkSched F st hnn hsep hprec).IsNonPreemptive := by
  intro j i
  rw [mkSched_pieces]
  split_ifs <;> simp

theorem finish_le {m : ℕ} {J : Type*} [Fintype J] {F : FlowShop m J} (S : PreemptiveSchedule F)
    (B : ℝ) (hB : 0 ≤ B) (h : ∀ j i, ∀ p ∈ S.pieces j i, p.2 ≤ B) : S.finishTime ≤ B := by
  unfold PreemptiveSchedule.finishTime
  rw [Finset.fold_max_le]
  refine ⟨hB, fun i _ => ?_⟩
  unfold PreemptiveSchedule.jobFinish
  rw [Finset.fold_max_le]
  refine ⟨hB, fun p hp => ?_⟩
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 hp
  exact h j i p hj

end Builder


section OneA


/-- prefix sum over the indices of `v` below `i` -/
noncomputable def pre {n : ℕ} (a : Fin n → ℕ) (v : Finset (Fin n)) (i : Fin n) : ℝ :=
  ∑ j ∈ v.filter (· < i), (a j : ℝ)

theorem pre_nonneg {n : ℕ} (a : Fin n → ℕ) (v : Finset (Fin n)) (i : Fin n) : 0 ≤ pre a v i :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem pre_add_le_sum {n : ℕ} (a : Fin n → ℕ) (v : Finset (Fin n)) (i : Fin n) (hi : i ∈ v) :
    pre a v i + (a i : ℝ) ≤ ∑ j ∈ v, (a j : ℝ) := by
  classical
  have : pre a v i + (a i : ℝ) = ∑ j ∈ insert i (v.filter (· < i)), (a j : ℝ) := by
    rw [Finset.sum_insert (by simp)]; unfold pre; ring
  rw [this]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hi
    · exact (Finset.mem_filter.1 hx).1
  · intros; exact Nat.cast_nonneg _

theorem pre_mono {n : ℕ} (a : Fin n → ℕ) (v : Finset (Fin n)) (i i' : Fin n) (hi : i ∈ v)
    (h : i < i') : pre a v i + (a i : ℝ) ≤ pre a v i' := by
  classical
  have : pre a v i + (a i : ℝ) = ∑ j ∈ insert i (v.filter (· < i)), (a j : ℝ) := by
    rw [Finset.sum_insert (by simp)]; unfold pre; ring
  rw [this]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simp [hi, h]
    · simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans h⟩
  · intros; exact Nat.cast_nonneg _

/-- start times of the schedule built from the subset `u` -/
noncomputable def stA {n : ℕ} (a : Fin n → ℕ) (u : Finset (Fin n)) :
    Fin 3 → Fin n ⊕ Fin 2 → ℝ
  | j, Sum.inl i => ![if i ∈ u then pre a u i else T a + pre a uᶜ i, 0,
      if i ∈ u then T a / 2 + pre a u i else 3 * T a / 2 + pre a uᶜ i] j
  | j, Sum.inr 0 => ![T a / 2, T a, 0] j
  | j, Sum.inr 1 => ![0, 0, T a] j

theorem lemma_1a_core {n : ℕ} (a : Fin n → ℕ) (h : HasPartition a) :
    ∃ S : PreemptiveSchedule (FS a), S.IsNonPreemptive ∧ S.finishTime = 2 * T a := by
  classical
  obtain ⟨u, hu⟩ := h
  have hT := T_nonneg a
  have hTsum : T a = ∑ i, (a i : ℝ) := rfl
  have hAu : ∑ i ∈ u, (a i : ℝ) = T a / 2 := by
    have : (2 : ℝ) * ∑ i ∈ u, (a i : ℝ) = ∑ i, (a i : ℝ) := by exact_mod_cast hu
    linarith
  have hAw : ∑ i ∈ uᶜ, (a i : ℝ) = T a / 2 := by
    have := Finset.sum_add_sum_compl u (fun i => (a i : ℝ))
    linarith
  -- facts
  have fu : ∀ i ∈ u, pre a u i + (a i : ℝ) ≤ T a / 2 := fun i hi => hAu ▸ pre_add_le_sum a u i hi
  have fw : ∀ i ∉ u, pre a uᶜ i + (a i : ℝ) ≤ T a / 2 := fun i hi =>
    hAw ▸ pre_add_le_sum a uᶜ i (by simpa using hi)
  have ha0 : ∀ i, (0 : ℝ) ≤ a i := fun i => Nat.cast_nonneg _
  have fhalf : ∀ i, (a i : ℝ) ≤ T a / 2 := by
    intro i
    by_cases hi : i ∈ u
    · have := fu i hi; have := pre_nonneg a u i; linarith
    · have := fw i hi; have := pre_nonneg a uᶜ i; linarith
  -- P1 start of job i
  have sepJ : ∀ i i' : Fin n, i ≠ i' →
      stA a u 0 (Sum.inl i) + (a i : ℝ) ≤ stA a u 0 (Sum.inl i') ∨
      stA a u 0 (Sum.inl i') + (a i' : ℝ) ≤ stA a u 0 (Sum.inl i) := by
    have key : ∀ i i' : Fin n, i < i' →
        stA a u 0 (Sum.inl i) + (a i : ℝ) ≤ stA a u 0 (Sum.inl i') ∨
        stA a u 0 (Sum.inl i') + (a i' : ℝ) ≤ stA a u 0 (Sum.inl i) := by
      intro i i' hlt
      by_cases hi : i ∈ u <;> by_cases hi' : i' ∈ u <;> simp only [stA, hi, hi', if_true, if_false]
      · left; exact pre_mono a u i i' hi hlt
      · left
        have := fu i hi; have := pre_nonneg a uᶜ i'; simp; linarith
      · right
        have := fu i' hi'; have := pre_nonneg a uᶜ i; simp; linarith
      · left
        have := pre_mono a uᶜ i i' (by simpa using hi) hlt; simp; linarith
    intro i i' hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key i i' hlt
    · exact (key i' i hlt).symm
  have tt : ∀ j i, (FS a).t j i = fsTimes a j i := fun _ _ => rfl
  have hnn : ∀ j i, (FS a).t j i ≠ 0 → 0 ≤ stA a u j i := by
    intro j i _
    have h1 := pre_nonneg a u
    have h2 := pre_nonneg a uᶜ
    rcases i with i | k
    · fin_cases j <;> simp [stA] <;> split_ifs <;> linarith [h1 i, h2 i]
    · fin_cases k <;> fin_cases j <;> simp [stA] <;> linarith
  have hfact : ∀ i : Fin n, (i ∈ u ∧ pre a u i + (a i : ℝ) ≤ T a / 2 ∧ 0 ≤ pre a u i) ∨
      (i ∉ u ∧ pre a uᶜ i + (a i : ℝ) ≤ T a / 2 ∧ 0 ≤ pre a uᶜ i) := by
    intro i
    by_cases hi : i ∈ u
    · exact Or.inl ⟨hi, fu i hi, pre_nonneg a u i⟩
    · exact Or.inr ⟨hi, fw i hi, pre_nonneg a uᶜ i⟩
  have hsep : ∀ j i i', i ≠ i' → (FS a).t j i = 0 ∨ (FS a).t j i' = 0 ∨
      stA a u j i + (FS a).t j i ≤ stA a u j i' ∨ stA a u j i' + (FS a).t j i' ≤ stA a u j i := by
    intro j i i' hne
    fin_cases j
    · rcases i with i | k <;> rcases i' with i' | k'
      · right; right
        simpa [tt, fsTimes, stA] using sepJ i i' (by simpa using hne)
      · fin_cases k'
        · rcases hfact i with ⟨hi, f1, f2⟩ | ⟨hi, f1, f2⟩ <;> simp [tt, fsTimes, stA, hi] <;> (first | (left; linarith) | (right; left; linarith) | (right; right; left; linarith) | (right; right; right; linarith) | (right; right; linarith) | (right; linarith) | linarith)
        · simp [tt, fsTimes, stA]
      · fin_cases k
        · rcases hfact i' with ⟨hi, f1, f2⟩ | ⟨hi, f1, f2⟩ <;> simp [tt, fsTimes, stA, hi] <;> (first | (left; linarith) | (right; left; linarith) | (right; right; left; linarith) | (right; right; right; linarith) | (right; right; linarith) | (right; linarith) | linarith)
        · simp [tt, fsTimes, stA]
      · fin_cases k <;> fin_cases k' <;> simp [tt, fsTimes, stA] at hne ⊢
    · rcases i with i | k <;> rcases i' with i' | k'
      · simp [tt, fsTimes, stA]
      · simp [tt, fsTimes, stA]
      · simp [tt, fsTimes, stA]
      · fin_cases k <;> fin_cases k' <;> simp [tt, fsTimes, stA] at hne ⊢ <;> (first | (left; linarith) | (right; left; linarith) | (right; right; left; linarith) | (right; right; right; linarith) | (right; right; linarith) | (right; linarith) | linarith)
    · rcases i with i | k <;> rcases i' with i' | k'
      · have := sepJ i i' (by simpa using hne)
        rcases hfact i with ⟨hi, f1, f2⟩ | ⟨hi, f1, f2⟩ <;>
        rcases hfact i' with ⟨hi', f1', f2'⟩ | ⟨hi', f1', f2'⟩ <;>
        simp [tt, fsTimes, stA, hi, hi'] at this ⊢ <;> rcases this with h | h <;> (first | (left; linarith) | (right; left; linarith) | (right; right; left; linarith) | (right; right; right; linarith) | (right; right; linarith) | (right; linarith) | linarith)
      · fin_cases k'
        · simp [tt, fsTimes, stA]
        · rcases hfact i with ⟨hi, f1, f2⟩ | ⟨hi, f1, f2⟩ <;> simp [tt, fsTimes, stA, hi] <;> (first | (left; linarith) | (right; left; linarith) | (right; right; left; linarith) | (right; right; right; linarith) | (right; right; linarith) | (right; linarith) | linarith)
      · fin_cases k
        · simp [tt, fsTimes, stA]
        · rcases hfact i' with ⟨hi, f1, f2⟩ | ⟨hi, f1, f2⟩ <;> simp [tt, fsTimes, stA, hi] <;> (first | (left; linarith) | (right; left; linarith) | (right; right; left; linarith) | (right; right; right; linarith) | (right; right; linarith) | (right; linarith) | linarith)
      · fin_cases k <;> fin_cases k' <;> simp [tt, fsTimes, stA] at hne ⊢
  have hprec : ∀ i j j', j < j' → (FS a).t j i = 0 ∨ (FS a).t j' i = 0 ∨
      stA a u j i + (FS a).t j i ≤ stA a u j' i := by
    intro i j j' hjj
    rcases i with i | k
    · have hh := fhalf i
      fin_cases j <;> fin_cases j' <;> simp at hjj <;>
      first
      | (simp [tt, fsTimes, stA]; done)
      | (rcases hfact i with ⟨hi, f1, f2⟩ | ⟨hi, f1, f2⟩ <;> simp [tt, fsTimes, stA, hi] <;> (first | (left; linarith) | (right; left; linarith) | (right; right; left; linarith) | (right; right; right; linarith) | (right; right; linarith) | (right; linarith) | linarith))
    · fin_cases k <;> fin_cases j <;> fin_cases j' <;> simp at hjj <;>
      first
      | (simp [tt, fsTimes, stA]; done)
      | (simp [tt, fsTimes, stA]; (first | (left; linarith) | (right; left; linarith) | (right; right; left; linarith) | (right; right; right; linarith) | (right; right; linarith) | (right; linarith) | linarith))
  have hb : ∀ (S : PreemptiveSchedule (FS a)), S = mkSched (FS a) (stA a u) hnn hsep hprec →
      ∀ j i, ∀ p ∈ S.pieces j i, p.2 ≤ 2 * T a := by
    intro S hS j i p hp
    subst hS
    rw [mkSched_pieces] at hp
    obtain ⟨h1, rfl⟩ := mem_pc.1 hp
    show stA a u j i + (FS a).t j i ≤ 2 * T a
    rcases i with i | k
    · rcases hfact i with ⟨hi, f1, f2⟩ | ⟨hi, f1, f2⟩ <;>
      fin_cases j <;> simp [tt, fsTimes, stA, hi] <;> linarith
    · fin_cases k <;> fin_cases j <;> simp [tt, fsTimes, stA] <;> linarith
  refine ⟨mkSched (FS a) (stA a u) hnn hsep hprec, mkSched_nonpre _ _ _ _ _, ?_⟩
  apply le_antisymm
  · exact finish_le _ (2 * T a) (by linarith) (hb _ rfl)
  · rcases hT.eq_or_lt with h0 | hpos
    · rw [← h0]
      unfold PreemptiveSchedule.finishTime
      rw [Finset.le_fold_max]; left; simp
    · have hmem : (T a, T a + T a) ∈ (mkSched (FS a) (stA a u) hnn hsep hprec).pieces 1 (Sum.inr 0) := by
        rw [mkSched_pieces]
        apply mem_pc.2
        refine ⟨?_, ?_⟩
        · simp [tt, fsTimes]; exact hpos.ne'
        · simp [tt, fsTimes, stA]
      have := piece_end_le _ _ _ _ hmem
      simp only at this
      linarith

end OneA

theorem lemma_1_core {n : ℕ} (a : Fin n → ℕ) :
    (∃ S : PreemptiveSchedule (FS a), S.finishTime ≤ 2 * T a) ↔ HasPartition a := by
  constructor
  · rintro ⟨S, hS⟩
    by_contra h
    have := lemma_1b_core a h S
    linarith
  · intro h
    obtain ⟨S, _, he⟩ := lemma_1a_core a h
    exact ⟨S, he.le⟩

theorem corollary_1_core {n : ℕ} (a : Fin n → ℕ) :
    (∃ S : PreemptiveSchedule (FS a), S.IsNonPreemptive ∧ S.finishTime ≤ 2 * T a) ↔
      HasPartition a := by
  constructor
  · rintro ⟨S, _, hS⟩
    by_contra h
    have := lemma_1b_core a h S
    linarith
  · intro h
    obtain ⟨S, hn, he⟩ := lemma_1a_core a h
    exact ⟨S, hn, he.le⟩

theorem atMostTwo_core {n : ℕ} (a : Fin n → ℕ) : (FS a).AtMostTwoNonzeroTasks := by
  intro i
  rcases i with i | k
  · have : (Finset.univ : Finset (Fin 3)).filter (fun j => (FS a).t j (Sum.inl i) ≠ 0)
        ⊆ ({0, 2} : Finset (Fin 3)) := by
      intro j hj
      simp only [Finset.mem_filter] at hj
      fin_cases j <;> simp [FS, fsTimes] at hj ⊢
    exact (Finset.card_le_card this).trans Finset.card_le_two
  · fin_cases k
    · have : (Finset.univ : Finset (Fin 3)).filter (fun j => (FS a).t j (Sum.inr 0) ≠ 0)
          ⊆ ({0, 1} : Finset (Fin 3)) := by
        intro j hj
        simp only [Finset.mem_filter] at hj
        fin_cases j <;> simp [FS, fsTimes] at hj ⊢
      exact (Finset.card_le_card this).trans Finset.card_le_two
    · have : (Finset.univ : Finset (Fin 3)).filter (fun j => (FS a).t j (Sum.inr 1) ≠ 0)
          ⊆ ({1, 2} : Finset (Fin 3)) := by
        intro j hj
        simp only [Finset.mem_filter] at hj
        fin_cases j <;> simp [FS, fsTimes] at hj ⊢
      exact (Finset.card_le_card this).trans Finset.card_le_two

end FlowJobShop.PartitionFlow

open FlowJobShop.PartitionFlow


theorem solution {n : ℕ} (a : Fin n → ℕ) :
    (FS a).AtMostTwoNonzeroTasks ∧
      ((∃ S : PreemptiveSchedule (FS a), S.finishTime ≤ 2 * T a) ↔ HasPartition a) ∧
      ((∃ S : PreemptiveSchedule (FS a), S.IsNonPreemptive ∧ S.finishTime ≤ 2 * T a) ↔
        HasPartition a) := by
  exact ⟨atMostTwo_core a, lemma_1_core a, corollary_1_core a⟩
