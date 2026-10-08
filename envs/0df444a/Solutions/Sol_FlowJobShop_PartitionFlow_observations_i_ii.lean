-- Prove2me | solution 1 for FlowJobShop.PartitionFlow.observations_i_ii
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:24:49.736975+00:00
-- url     : https://prove2.me/submissions/1f34be63-a68e-44de-a3dc-8586197bd89e

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

end FlowJobShop.PartitionFlow

open FlowJobShop.PartitionFlow


theorem solution {n : ℕ} (a : Fin n → ℕ) (S : PreemptiveSchedule (FS a))
    (hS : S.finishTime ≤ 2 * T a) :
    (∀ p ∈ S.pieces 0 (Sum.inr 0), p.2 ≤ T a) ∧
      (∀ p ∈ S.pieces 2 (Sum.inr 1), T a ≤ p.1) := by
  exact observations_core a S hS
