-- Prove2me | solution 1 for FlowJobShop.ThreePartFlow.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T08:26:52.367597+00:00
-- url     : https://prove2.me/submissions/2e22534c-b697-40d3-ad4a-1677adc3eb9b

import Mathlib
import Definitions.Def_FlowJobShop_ThreePartFlow_FlowShop
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_FlowJobShop_ThreePartFlow_Instance

set_option autoImplicit false
set_option linter.unusedSectionVars false

open ResourceScheduling.Chain
open FlowJobShop.ThreePartFlow FlowJobShop.ThreePartFlow.FlowShop

namespace TPFAux

/-- length of `[p.1, p.2) ∩ [a, b)` -/
noncomputable def w (p : ℝ × ℝ) (a b : ℝ) : ℝ := max 0 (min p.2 b - max p.1 a)

lemma w_nonneg (p : ℝ × ℝ) (a b : ℝ) : 0 ≤ w p a b := le_max_left _ _

lemma w_le (p : ℝ × ℝ) (a b : ℝ) (hp : p.1 ≤ p.2) : w p a b ≤ p.2 - p.1 := by
  unfold w
  apply max_le (by linarith)
  have h1 := min_le_left p.2 b
  have h2 := le_max_left p.1 a
  linarith

lemma w_full (p : ℝ × ℝ) (a b : ℝ) (h1 : a ≤ p.1) (h2 : p.2 ≤ b) (hp : p.1 ≤ p.2) :
    w p a b = p.2 - p.1 := by
  unfold w
  rw [min_eq_left h2, max_eq_left h1, max_eq_right (by linarith)]

lemma w_zero (p : ℝ × ℝ) (a b : ℝ) (h : b ≤ p.1) : w p a b = 0 := by
  unfold w
  apply max_eq_left
  have h1 := min_le_right p.2 b
  have h2 := le_max_left p.1 a
  linarith

lemma w_split (p : ℝ × ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hp : p.1 ≤ p.2) :
    w p a c = w p a b + w p b c := by
  obtain ⟨s, f⟩ := p
  simp only at hp
  unfold w
  simp only
  rcases le_total b s with h | h
  · have e1 : max s a = s := max_eq_left (le_trans hab h)
    have e2 : max s b = s := max_eq_left h
    rw [e1, e2, max_eq_left (show min f b - s ≤ 0 by linarith [min_le_right f b]), zero_add]
  · rcases le_total f b with h' | h'
    · have e1 : min f c = f := min_eq_left (le_trans h' hbc)
      have e2 : min f b = f := min_eq_left h'
      rw [e1, e2, max_eq_left (show f - max s b ≤ 0 by linarith [le_max_right s b]), add_zero]
    · have e1 : max s b = b := max_eq_right h
      have e2 : min f b = b := min_eq_right h'
      have e4 : max s a ≤ b := max_le h hab
      have e5 : b ≤ min f c := le_min h' hbc
      rw [e1, e2, max_eq_right (show 0 ≤ min f c - max s a by linarith),
        max_eq_right (show 0 ≤ b - max s a by linarith),
        max_eq_right (show 0 ≤ min f c - b by linarith)]
      ring

lemma ofReal_w (p : ℝ × ℝ) (a b : ℝ) :
    MeasureTheory.volume (Set.Ico p.1 p.2 ∩ Set.Ico a b) = ENNReal.ofReal (w p a b) := by
  rw [Set.Ico_inter_Ico, Real.volume_Ico]
  unfold w
  rcases le_total 0 (min p.2 b - max p.1 a) with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, ENNReal.ofReal_zero]
    exact ENNReal.ofReal_of_nonpos h

lemma sum_w_le {ι : Type*} (s : Finset ι) (I : ι → ℝ × ℝ)
    (hd : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (I x).2 ≤ (I y).1 ∨ (I y).2 ≤ (I x).1)
    {a b : ℝ} (hab : a ≤ b) :
    ∑ x ∈ s, w (I x) a b ≤ b - a := by
  have hnn : ∀ x ∈ s, 0 ≤ w (I x) a b := fun x _ => w_nonneg _ _ _
  rw [← ENNReal.ofReal_le_ofReal_iff (by linarith), ENNReal.ofReal_sum_of_nonneg hnn]
  simp_rw [← ofReal_w]
  rw [← MeasureTheory.measure_biUnion_finset]
  · rw [← Real.volume_Ico]
    apply MeasureTheory.measure_mono
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, _, hz⟩ := hz
    exact hz.2
  · intro x hx y hy hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    simp only [Set.mem_inter_iff, Set.mem_Ico] at hz hz'
    rcases hd x hx y hy hxy with h | h <;> linarith [hz.1.1, hz.1.2, hz'.1.1, hz'.1.2]
  · intro x _
    exact measurableSet_Ico.inter measurableSet_Ico

section Sched

variable {m : ℕ} {J : Type*} [Fintype J] {F : FlowShop m J}

/-- work of task `j` of job `i` inside `[a, b)` -/
noncomputable def W (S : PreemptiveSchedule F) (j : Fin m) (i : J) (a b : ℝ) : ℝ :=
  ∑ p ∈ S.pieces j i, w p a b

variable (S : PreemptiveSchedule F)

lemma W_nonneg (j : Fin m) (i : J) (a b : ℝ) : 0 ≤ W S j i a b :=
  Finset.sum_nonneg fun p _ => w_nonneg p a b

lemma W_le_t (j : Fin m) (i : J) (a b : ℝ) : W S j i a b ≤ F.t j i := by
  rw [← S.total_length j i]
  exact Finset.sum_le_sum fun p hp => w_le p a b (S.start_lt_end j i p hp).le

lemma W_split (j : Fin m) (i : J) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    W S j i a c = W S j i a b + W S j i b c := by
  unfold W
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p hp => w_split p hab hbc (S.start_lt_end j i p hp).le

lemma W_full (j : Fin m) (i : J) (T : ℝ) (h : ∀ p ∈ S.pieces j i, p.2 ≤ T) :
    W S j i 0 T = F.t j i := by
  rw [← S.total_length j i]
  exact Finset.sum_congr rfl fun p hp =>
    w_full p 0 T (S.start_nonneg j i p hp) (h p hp) (S.start_lt_end j i p hp).le

lemma W_zero (j : Fin m) (i : J) (a T : ℝ) (h : ∀ p ∈ S.pieces j i, T ≤ p.1) :
    W S j i a T = 0 :=
  Finset.sum_eq_zero fun p hp => w_zero p a T (h p hp)

lemma prec_or (i : J) {j j' : Fin m} (hjj : j < j') (T : ℝ) :
    (∀ p ∈ S.pieces j i, p.2 ≤ T) ∨ (∀ p ∈ S.pieces j' i, T ≤ p.1) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨p, hp, hpT⟩, ⟨q, hq, hqT⟩⟩ := hc
  have := S.precedence i j j' hjj p hp q hq
  linarith

lemma machine_le (j : Fin m) {a b : ℝ} (hab : a ≤ b) : ∑ i, W S j i a b ≤ b - a := by
  have key := sum_w_le (Finset.univ.sigma fun i => S.pieces j i) (fun x => x.2) ?_ hab
  · rw [Finset.sum_sigma] at key
    exact key
  · intro x hx y hy hxy
    rw [Finset.mem_sigma] at hx hy
    refine S.disjoint j x.1 y.1 x.2 y.2 hx.2 hy.2 ?_
    intro h
    apply hxy
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

lemma ends_le (τ : ℝ) (hS : S.finishTime ≤ τ) (j : Fin m) (i : J) :
    ∀ p ∈ S.pieces j i, p.2 ≤ τ := by
  intro p hp
  unfold PreemptiveSchedule.finishTime at hS
  rw [Finset.fold_max_le] at hS
  have h2 := hS.2 i (Finset.mem_univ i)
  unfold PreemptiveSchedule.jobFinish at h2
  rw [Finset.fold_max_le] at h2
  exact h2.2 p (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hp⟩)

lemma busy (τ : ℝ) (hS : S.finishTime ≤ τ) (j : Fin m) (htot : ∑ i, F.t j i = τ)
    {T : ℝ} (h0 : 0 ≤ T) (hT : T ≤ τ) : T ≤ ∑ i, W S j i 0 T := by
  have e1 : ∑ i, W S j i 0 τ = τ := by
    rw [Finset.sum_congr rfl fun i _ => W_full S j i τ (ends_le S τ hS j i)]
    exact htot
  have e2 : ∑ i, W S j i 0 τ = ∑ i, W S j i 0 T + ∑ i, W S j i T τ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => W_split S j i h0 hT
  have e3 := machine_le S j hT
  linarith

end Sched

end TPFAux

namespace TPFAux

def fsEquiv (t : ℕ) :
    Fin (3 * t) ⊕ (Unit ⊕ (Fin (t - 2) ⊕ (Unit ⊕ (Unit ⊕ Unit)))) ≃ FSJob t where
  toFun
    | .inl e => .elem e
    | .inr (.inl _) => .first
    | .inr (.inr (.inl k)) => .middle k
    | .inr (.inr (.inr (.inl _))) => .last
    | .inr (.inr (.inr (.inr (.inl _)))) => .tail3
    | .inr (.inr (.inr (.inr (.inr _)))) => .tail1
  invFun
    | .elem e => .inl e
    | .first => .inr (.inl ())
    | .middle k => .inr (.inr (.inl k))
    | .last => .inr (.inr (.inr (.inl ())))
    | .tail3 => .inr (.inr (.inr (.inr (.inl ()))))
    | .tail1 => .inr (.inr (.inr (.inr (.inr ()))))
  left_inv := by
    intro x
    rcases x with e | ⟨⟩ | k | ⟨⟩ | ⟨⟩ | ⟨⟩ <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

lemma sum_FSJob {t : ℕ} (f : FSJob t → ℝ) :
    ∑ X, f X = ∑ e, f (.elem e) + f .first + ∑ k, f (.middle k) + f .last + f .tail3
      + f .tail1 := by
  rw [← Fintype.sum_equiv (fsEquiv t) (fun y => f (fsEquiv t y)) f (fun _ => rfl)]
  simp [Fintype.sum_sum_type, fsEquiv]
  ring

lemma sum_ite_card {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] (c : ℝ) :
    ∑ x, (if P x then c else 0) = ((Finset.univ.filter P).card : ℝ) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

lemma tot (C : ThreePartition) (hC : C.Valid) (ht : 2 ≤ C.t) (j : Fin 3) :
    ∑ X, (FS C).t j X = tau C := by
  rw [sum_FSJob]
  have hs : ∑ e, (C.a e : ℝ) = C.t * C.b := by exact_mod_cast hC.2.1
  have hc : ((C.t - 2 : ℕ) : ℝ) = C.t - 2 := by push_cast [Nat.cast_sub ht]; ring
  fin_cases j <;> simp [FS, fsTime, hs, hc, tau] <;> ring

section Gen
variable {m : ℕ} {J : Type*} [Fintype J] {F : FlowShop m J} (S : PreemptiveSchedule F)

open Classical in
lemma W_ite_le {j j' : Fin m} (hjj : j < j') (X : J) (a T : ℝ) :
    W S j' X a T ≤ if (∀ p ∈ S.pieces j X, p.2 ≤ T) then F.t j' X else 0 := by
  split_ifs with h
  · exact W_le_t S j' X a T
  · rw [W_zero S j' X a T ((prec_or S X hjj T).resolve_left h)]

open Classical in
lemma W_ite_ge (j : Fin m) (X : J) (T : ℝ) :
    (if (∀ p ∈ S.pieces j X, p.2 ≤ T) then F.t j X else 0) ≤ W S j X 0 T := by
  split_ifs with h
  · rw [W_full S j X T h]
  · exact W_nonneg S j X 0 T

open Classical in
lemma W_split_ite {j j' : Fin m} (hjj : j < j') (X : J) {T0 T' : ℝ} (h0 : 0 ≤ T0)
    (h1 : T0 ≤ T') :
    W S j' X 0 T' ≤ (if (∀ p ∈ S.pieces j X, p.2 ≤ T0) then F.t j' X else 0)
      + W S j' X T0 T' := by
  rw [W_split S j' X h0 h1]
  linarith [W_ite_le S hjj X 0 T0]

end Gen

section Round
variable (C : ThreePartition) (S : PreemptiveSchedule (FS C))

open Classical in
noncomputable def D0 (n : ℕ) : Finset (Fin (3 * C.t)) :=
  Finset.univ.filter (fun e => ∀ p ∈ S.pieces 0 (.elem e), p.2 ≤ 2 * n * (C.b : ℝ) + 1 / 4)

set_option maxHeartbeats 1000000 in
open Classical in
lemma round (hC : C.Valid) (ht : 2 ≤ C.t) (hS : S.finishTime ≤ tau C) (n : ℕ) (hn1 : 1 ≤ n)
    (hn : n < C.t) : ∑ e ∈ D0 C S n, C.a e = n * C.b := by
  set B : ℝ := (C.b : ℝ) with hBdef
  have hB : (1 : ℝ) ≤ B := by have : 1 ≤ C.b := hC.1; rw [hBdef]; exact_mod_cast this
  have hnt : (n : ℝ) + 1 ≤ C.t := by exact_mod_cast hn
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set T' : ℝ := 2 * n * B + 1 / 4 with hT'
  set T0 : ℝ := 2 * n * B - 1 / 4 with hT0
  have hT'τ : T' ≤ tau C := by
    have := mul_le_mul_of_nonneg_right hnt (by linarith : (0:ℝ) ≤ B)
    simp only [tau, hT']; linarith
  have hnB : (1:ℝ) ≤ n * B := by
    have := mul_le_mul hn1' hB zero_le_one (by linarith); linarith
  have hT0p : 0 ≤ T0 := by linarith
  -- (b) machine 2 busy up to T'
  have b1 := busy S (tau C) hS 1 (tot C hC ht 1) (by linarith) hT'τ
  rw [sum_FSJob] at b1
  have be : ∀ e, W S 1 (.elem e) 0 T' ≤ 0 := fun e => by
    simpa [FS, fsTime] using W_le_t S 1 (.elem e) 0 T'
  have bt3 : W S 1 .tail3 0 T' ≤ 0 := by simpa [FS, fsTime] using W_le_t S 1 .tail3 0 T'
  have bt1 : W S 1 .tail1 0 T' ≤ 0 := by simpa [FS, fsTime] using W_le_t S 1 .tail1 0 T'
  have bf : W S 1 .first 0 T' ≤ 2 * B := by simpa [FS, fsTime] using W_le_t S 1 .first 0 T'
  have bm : ∀ k, W S 1 (.middle k) 0 T' ≤
      if (∀ p ∈ S.pieces 0 (.middle k), p.2 ≤ T') then 2 * B else 0 := fun k => by
    simpa [FS, fsTime] using W_ite_le S (show (0 : Fin 3) < 1 by decide) (.middle k) 0 T'
  have bl : W S 1 .last 0 T' ≤
      if (∀ p ∈ S.pieces 0 .last, p.2 ≤ T') then 2 * B else 0 := by
    simpa [FS, fsTime] using W_ite_le S (show (0 : Fin 3) < 1 by decide) .last 0 T'
  have bmsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => bm k
  have besum := Finset.sum_le_sum fun e (_ : e ∈ Finset.univ) => be e
  rw [sum_ite_card] at bmsum
  simp only [Finset.sum_const_zero] at besum
  set Nm : ℕ := (Finset.univ.filter
    (fun k => ∀ p ∈ S.pieces 0 (FSJob.middle k), p.2 ≤ T')).card with hNm
  -- (c) machine 1 capacity up to T'
  have c1 := machine_le S 0 (show (0 : ℝ) ≤ T' by linarith)
  rw [sum_FSJob] at c1
  have cm : ∀ k, (if (∀ p ∈ S.pieces 0 (.middle k), p.2 ≤ T') then B else 0) ≤
      W S 0 (.middle k) 0 T' := fun k => by
    simpa [FS, fsTime] using W_ite_ge S 0 (.middle k) T'
  have cl : (if (∀ p ∈ S.pieces 0 .last, p.2 ≤ T') then B else 0) ≤ W S 0 .last 0 T' := by
    simpa [FS, fsTime] using W_ite_ge S 0 .last T'
  have cmsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => cm k
  rw [sum_ite_card] at cmsum
  have cf := W_nonneg S 0 .first 0 T'
  have ct3 := W_nonneg S 0 .tail3 0 T'
  have ct1 := W_nonneg S 0 .tail1 0 T'
  have cD : (∑ e ∈ D0 C S n, (C.a e : ℝ)) ≤ ∑ e, W S 0 (.elem e) 0 T' := by
    calc (∑ e ∈ D0 C S n, (C.a e : ℝ)) = ∑ e ∈ D0 C S n, W S 0 (.elem e) 0 T' := by
          refine Finset.sum_congr rfl fun e he => ?_
          simp only [D0, Finset.mem_filter] at he
          rw [W_full S 0 _ T' he.2]
          simp [FS, fsTime]
      _ ≤ ∑ e, W S 0 (.elem e) 0 T' :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun e _ _ => W_nonneg S 0 _ 0 T'
  -- upper bound
  have hup : (∑ e ∈ D0 C S n, (C.a e : ℝ)) ≤ n * B + 1 / 4 := by
    have hNl : (n : ℝ) ≤ Nm + (if (∀ p ∈ S.pieces 0 .last, p.2 ≤ T') then 1 else 0) := by
      by_contra hcon
      push Not at hcon
      have : (Nm : ℝ) + (if (∀ p ∈ S.pieces 0 .last, p.2 ≤ T') then 1 else 0) + 1 ≤ n := by
        split_ifs at hcon ⊢
        · have h2 : Nm + 1 < n := by exact_mod_cast hcon
          have h3 : ((Nm + 1 + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h2
          push_cast at h3; linarith
        · have h2 : Nm < n := by exact_mod_cast (by simpa using hcon)
          have h3 : ((Nm + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h2
          push_cast at h3; linarith
      have hm := mul_le_mul_of_nonneg_right this (show (0:ℝ) ≤ 2 * B by linarith)
      split_ifs at bl hm <;> linarith
    have hm2 := mul_le_mul_of_nonneg_right hNl (show (0:ℝ) ≤ B by linarith)
    split_ifs at cl hm2 <;> linarith
  -- (f) machine 3 busy up to T'
  have f1 := busy S (tau C) hS 2 (tot C hC ht 2) (by linarith) hT'τ
  rw [sum_FSJob] at f1
  have fe : ∀ e, W S 2 (.elem e) 0 T' ≤
      if (∀ p ∈ S.pieces 0 (.elem e), p.2 ≤ T') then (C.a e : ℝ) else 0 := fun e => by
    simpa [FS, fsTime] using W_ite_le S (show (0 : Fin 3) < 2 by decide) (.elem e) 0 T'
  have fesum := Finset.sum_le_sum fun e (_ : e ∈ Finset.univ) => fe e
  rw [← Finset.sum_filter] at fesum
  have fl : W S 2 .last 0 T' ≤ 0 := by simpa [FS, fsTime] using W_le_t S 2 .last 0 T'
  have ft1 : W S 2 .tail1 0 T' ≤ 0 := by simpa [FS, fsTime] using W_le_t S 2 .tail1 0 T'
  have ft3 : W S 2 .tail3 0 T' ≤ B := by simpa [FS, fsTime] using W_le_t S 2 .tail3 0 T'
  have hT0T' : T0 ≤ T' := by linarith
  have ff : W S 2 .first 0 T' ≤ (if (∀ p ∈ S.pieces 1 .first, p.2 ≤ T0) then B else 0)
      + W S 2 .first T0 T' := by
    simpa [FS, fsTime] using
      W_split_ite S (show (1 : Fin 3) < 2 by decide) .first hT0p hT0T'
  have fm : ∀ k, W S 2 (.middle k) 0 T' ≤
      (if (∀ p ∈ S.pieces 1 (.middle k), p.2 ≤ T0) then B else 0)
      + W S 2 (.middle k) T0 T' := fun k => by
    simpa [FS, fsTime] using
      W_split_ite S (show (1 : Fin 3) < 2 by decide) (.middle k) hT0p hT0T'
  have fmsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => fm k
  rw [Finset.sum_add_distrib, sum_ite_card] at fmsum
  have g1 := machine_le S 2 hT0T'
  rw [sum_FSJob] at g1
  have g2 := Finset.sum_nonneg fun e (_ : e ∈ Finset.univ) => W_nonneg S 2 (FSJob.elem e) T0 T'
  have g3 := W_nonneg S 2 .last T0 T'
  have g4 := W_nonneg S 2 .tail3 T0 T'
  have g5 := W_nonneg S 2 .tail1 T0 T'
  have h1 := machine_le S 1 hT0p
  rw [sum_FSJob] at h1
  have hf : (if (∀ p ∈ S.pieces 1 .first, p.2 ≤ T0) then 2 * B else 0) ≤ W S 1 .first 0 T0 := by
    simpa [FS, fsTime] using W_ite_ge S 1 .first T0
  have hm : ∀ k, (if (∀ p ∈ S.pieces 1 (.middle k), p.2 ≤ T0) then 2 * B else 0) ≤
      W S 1 (.middle k) 0 T0 := fun k => by
    simpa [FS, fsTime] using W_ite_ge S 1 (.middle k) T0
  have hmsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hm k
  rw [sum_ite_card] at hmsum
  have h2 := Finset.sum_nonneg fun e (_ : e ∈ Finset.univ) => W_nonneg S 1 (FSJob.elem e) 0 T0
  have h3 := W_nonneg S 1 .last 0 T0
  have h4 := W_nonneg S 1 .tail3 0 T0
  have h5 := W_nonneg S 1 .tail1 0 T0
  set Nm' : ℕ := (Finset.univ.filter
    (fun k => ∀ p ∈ S.pieces 1 (FSJob.middle k), p.2 ≤ T0)).card with hNm'
  have hD : (∑ e ∈ D0 C S n, (C.a e : ℝ)) = ∑ e ∈ Finset.univ.filter
      (fun e => ∀ p ∈ S.pieces 0 (FSJob.elem e), p.2 ≤ T'), (C.a e : ℝ) := rfl
  have hlo : (n : ℝ) * B - 1 / 4 ≤ ∑ e ∈ D0 C S n, (C.a e : ℝ) := by
    have hNn : (Nm' : ℝ) * B + (if (∀ p ∈ S.pieces 1 .first, p.2 ≤ T0) then B else 0) + B
        ≤ n * B := by
      have hlt : (Nm' : ℝ) + (if (∀ p ∈ S.pieces 1 .first, p.2 ≤ T0) then 1 else 0) < n := by
        by_contra hge
        push Not at hge
        have hm := mul_le_mul_of_nonneg_right hge (show (0:ℝ) ≤ 2 * B by linarith)
        split_ifs at hf hm <;> linarith
      have hcnt : (Nm' : ℝ) + (if (∀ p ∈ S.pieces 1 .first, p.2 ≤ T0) then 1 else 0) + 1
          ≤ n := by
        split_ifs at hlt ⊢
        · have h6 : Nm' + 1 < n := by exact_mod_cast hlt
          have h7 : ((Nm' + 1 + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt h6
          push_cast at h7; linarith
        · have h6 : Nm' < n := by exact_mod_cast (by simpa using hlt)
          have h7 : ((Nm' + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt h6
          push_cast at h7; linarith
      have := mul_le_mul_of_nonneg_right hcnt (by linarith : (0 : ℝ) ≤ B)
      split_ifs at this ⊢ <;> linarith
    split_ifs at ff hNn <;> linarith
  -- integrality
  have hup' : ((∑ e ∈ D0 C S n, C.a e : ℕ) : ℝ) < ((n * C.b : ℕ) : ℝ) + 1 := by
    push_cast; linarith
  have hlo' : ((n * C.b : ℕ) : ℝ) < ((∑ e ∈ D0 C S n, C.a e : ℕ) : ℝ) + 1 := by
    push_cast; linarith
  have i1 : (∑ e ∈ D0 C S n, C.a e) < n * C.b + 1 := by exact_mod_cast hup'
  have i2 : n * C.b < (∑ e ∈ D0 C S n, C.a e) + 1 := by exact_mod_cast hlo'
  omega

end Round

lemma partition_of_prefix (C : ThreePartition) (hC : C.Valid) (Q : ℕ → Finset (Fin (3 * C.t)))
    (h0 : Q 0 = ∅) (hmono : ∀ n n', n ≤ n' → Q n ⊆ Q n') (htop : Q C.t = Finset.univ)
    (hsum : ∀ n, n ≤ C.t → ∑ e ∈ Q n, C.a e = n * C.b) : C.HasSolution := by
  classical
  have hmem : ∀ e : Fin (3 * C.t), e ∈ Q (C.t - 1 + 1) := by
    intro e
    have : 0 < C.t := by have := e.isLt; omega
    rw [Nat.sub_add_cancel this, htop]; exact Finset.mem_univ e
  have hex : ∀ e, ∃ n, e ∈ Q (n + 1) := fun e => ⟨_, hmem e⟩
  let σ : Fin (3 * C.t) → Fin C.t := fun e => ⟨Nat.find (hex e), by
    have h1 := Nat.find_min' (hex e) (hmem e)
    have : 0 < C.t := by have := e.isLt; omega
    omega⟩
  have key : ∀ e (i : ℕ), Nat.find (hex e) = i ↔ e ∈ Q (i + 1) ∧ e ∉ Q i := by
    intro e i
    rw [Nat.find_eq_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun hi => ?_⟩
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · simp [h0] at hi
      · exact h2 (i - 1) (by omega) (by rwa [Nat.sub_add_cancel hpos])
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun m hm hq => h2 (hmono (m + 1) i (by omega) hq)⟩
  refine ⟨σ, fun ⟨i, hi⟩ => ?_⟩
  have hpart : Finset.univ.filter (fun e => σ e = ⟨i, hi⟩) = Q (i + 1) \ Q i := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    rw [Fin.ext_iff]
    exact key e i
  rw [hpart]
  have hs : ∑ e ∈ Q (i + 1) \ Q i, C.a e = C.b := by
    have h := Finset.sum_sdiff (f := C.a) (hmono i (i + 1) (by omega))
    rw [hsum (i + 1) (by omega), hsum i (by omega)] at h
    have h3 : (∑ e ∈ Q (i + 1) \ Q i, C.a e) + i * C.b = C.b + i * C.b := by rw [h]; ring
    exact Nat.add_right_cancel h3
  refine ⟨?_, hs⟩
  set s := Q (i + 1) \ Q i
  have hb := hC.1
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [hemp, Finset.sum_empty] at hs
    omega
  have hlt1 : ∑ e ∈ s, C.b < ∑ e ∈ s, 4 * C.a e :=
    Finset.sum_lt_sum_of_nonempty hne fun e _ => (hC.2.2 e).1
  have hlt2 : ∑ e ∈ s, 2 * C.a e < ∑ e ∈ s, C.b :=
    Finset.sum_lt_sum_of_nonempty hne fun e _ => (hC.2.2 e).2
  rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, hs] at hlt1
  rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, hs] at hlt2
  have c1 : s.card < 4 := Nat.lt_of_mul_lt_mul_right hlt1
  have c2 : 2 < s.card := Nat.lt_of_mul_lt_mul_right hlt2
  omega

open Classical in
lemma only_if (C : ThreePartition) (hC : C.Valid) (ht : 2 ≤ C.t)
    (S : PreemptiveSchedule (FS C)) (hS : S.finishTime ≤ tau C) : C.HasSolution := by
  let Q : ℕ → Finset (Fin (3 * C.t)) := fun n =>
    if n = 0 then ∅ else if n < C.t then D0 C S n else Finset.univ
  apply partition_of_prefix C hC Q
  · simp [Q]
  · intro n n' hnn'
    simp only [Q]
    split_ifs <;> first | exact Finset.empty_subset _ | exact Finset.subset_univ _ | omega | skip
    intro e he
    simp only [D0, Finset.mem_filter] at he ⊢
    refine ⟨he.1, fun p hp => (he.2 p hp).trans ?_⟩
    have hnn : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
    have hb0 : (0 : ℝ) ≤ C.b := by positivity
    have := mul_le_mul_of_nonneg_right hnn hb0
    linarith
  · simp only [Q]
    rw [if_neg (by omega), if_neg (by omega)]
  · intro n hn
    simp only [Q]
    split_ifs with h1 h2
    · subst h1; simp
    · exact round C S hC ht hS n (by omega) h2
    · have : n = C.t := by omega
      rw [this]
      exact hC.2.1

end TPFAux

namespace TPFAux

section Build
variable (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t)

noncomputable def off (e : Fin (3 * C.t)) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => σ x = σ e ∧ x < e), (C.a x : ℝ)

noncomputable def st (e : Fin (3 * C.t)) : ℝ := 2 * ((σ e : ℕ) : ℝ) * C.b + off C σ e

noncomputable def pcs : Fin 3 → FSJob C.t → Finset (ℝ × ℝ) := fun j X =>
  match X with
  | .elem e => ![{(st C σ e, st C σ e + C.a e)}, ∅,
      {(st C σ e + C.b, st C σ e + C.b + C.a e)}] j
  | .first => ![∅, {(0, 2 * (C.b : ℝ))}, {(2 * (C.b : ℝ), 3 * (C.b : ℝ))}] j
  | .middle k => ![{(2 * ((k : ℕ) : ℝ) * C.b + C.b, 2 * ((k : ℕ) : ℝ) * C.b + 2 * C.b)},
      {(2 * (((k : ℕ) : ℝ) + 1) * C.b, 2 * (((k : ℕ) : ℝ) + 2) * C.b)},
      {(2 * (((k : ℕ) : ℝ) + 2) * C.b, 2 * (((k : ℕ) : ℝ) + 2) * C.b + C.b)}] j
  | .last => ![{(2 * ((C.t : ℝ) - 2) * C.b + C.b, 2 * ((C.t : ℝ) - 1) * C.b)},
      {(2 * ((C.t : ℝ) - 1) * C.b, 2 * (C.t : ℝ) * C.b)}, ∅] j
  | .tail3 => ![∅, ∅, {(0, (C.b : ℝ))}] j
  | .tail1 => ![{(2 * ((C.t : ℝ) - 1) * C.b + C.b, 2 * (C.t : ℝ) * C.b)}, ∅, ∅] j

def slot0 : FSJob C.t → ℕ
  | .elem e => 2 * (σ e : ℕ)
  | .first => 0
  | .middle k => 2 * (k : ℕ) + 1
  | .last => 2 * (C.t - 2) + 1
  | .tail3 => 0
  | .tail1 => 2 * (C.t - 1) + 1

def slot1 : FSJob C.t → ℕ
  | .elem _ => 0
  | .first => 0
  | .middle k => (k : ℕ) + 1
  | .last => C.t - 1
  | .tail3 => 0
  | .tail1 => 0

def slot2 : FSJob C.t → ℕ
  | .elem e => 2 * (σ e : ℕ) + 1
  | .first => 2
  | .middle k => 2 * (k : ℕ) + 4
  | .last => 0
  | .tail3 => 0
  | .tail1 => 0

lemma off_nonneg (e : Fin (3 * C.t)) : 0 ≤ off C σ e :=
  Finset.sum_nonneg fun x _ => Nat.cast_nonneg _

lemma off_add_le {e e' : Fin (3 * C.t)} (hs : σ e = σ e') (hlt : e < e') :
    off C σ e + C.a e ≤ off C σ e' := by
  unfold off
  have hnot : e ∉ Finset.univ.filter (fun x => σ x = σ e ∧ x < e) := by simp
  rw [add_comm, ← Finset.sum_insert (f := fun x => (C.a x : ℝ)) hnot]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨h1, h2⟩
    · exact ⟨hs, hlt⟩
    · exact ⟨h1.trans hs, h2.trans hlt⟩
  · intro x _ _; exact Nat.cast_nonneg _

lemma off_add_le_B (hσ : C.IsSolution σ) (e : Fin (3 * C.t)) :
    off C σ e + C.a e ≤ C.b := by
  unfold off
  have hnot : e ∉ Finset.univ.filter (fun x => σ x = σ e ∧ x < e) := by simp
  rw [add_comm, ← Finset.sum_insert (f := fun x => (C.a x : ℝ)) hnot]
  have hB : ∑ x ∈ Finset.univ.filter (fun x => σ x = σ e), (C.a x : ℝ) = C.b := by
    exact_mod_cast (hσ (σ e)).2
  rw [← hB]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨h1, _⟩
    · rfl
    · exact h1
  · intro x _ _; exact Nat.cast_nonneg _

lemma elem_disj {e e' : Fin (3 * C.t)} (hs : (σ e : ℕ) = σ e') (hne : (e : ℕ) ≠ e') :
    st C σ e + C.a e ≤ st C σ e' ∨ st C σ e' + C.a e' ≤ st C σ e := by
  have hs' : σ e = σ e' := Fin.ext hs
  unfold st
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    have := off_add_le C σ hs' (Fin.lt_def.2 h)
    rw [hs]; linarith
  · right
    have := off_add_le C σ hs'.symm (Fin.lt_def.2 h)
    rw [hs]; linarith

lemma sep {c : ℝ} (hc : 0 < c) {n n' : ℕ} (h : n ≠ n') {p p' : ℝ × ℝ} (h1 : c * n ≤ p.1)
    (h2 : p.2 ≤ c * n + c) (h1' : c * n' ≤ p'.1) (h2' : p'.2 ≤ c * n' + c) :
    p.2 ≤ p'.1 ∨ p'.2 ≤ p.1 := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left
    have : (n : ℝ) + 1 ≤ n' := by exact_mod_cast h
    have := mul_le_mul_of_nonneg_left this hc.le
    linarith
  · right
    have : (n' : ℝ) + 1 ≤ n := by exact_mod_cast h
    have := mul_le_mul_of_nonneg_left this hc.le
    linarith

lemma pcs_single (j : Fin 3) (X : FSJob C.t) (p p' : ℝ × ℝ) (hp : p ∈ pcs C σ j X)
    (hp' : p' ∈ pcs C σ j X) : p = p' := by
  rcases X with e | _ | k | _ | _ | _ <;> fin_cases j <;> simp [pcs] at hp hp' <;> rw [hp, hp']

end Build

end TPFAux

namespace TPFAux

section Build2
variable (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t)

lemma facts (hC : C.Valid) (ht : 2 ≤ C.t) :
    0 < (C.b : ℝ) ∧ (2 : ℝ) ≤ C.t ∧ (∀ e, 0 < (C.a e : ℝ)) ∧
      (∀ e, ((σ e : ℕ) : ℝ) + 1 ≤ C.t) ∧ (∀ k : Fin (C.t - 2), ((k : ℕ) : ℝ) + 3 ≤ C.t) ∧
      ((C.t - 2 : ℕ) : ℝ) = C.t - 2 ∧ ((C.t - 1 : ℕ) : ℝ) = C.t - 1 := by
  refine ⟨by exact_mod_cast hC.1, by exact_mod_cast ht, fun e => ?_, fun e => ?_, fun k => ?_,
    by push_cast [Nat.cast_sub ht]; ring, by push_cast [Nat.cast_sub (by omega : 1 ≤ C.t)]; ring⟩
  · have := (hC.2.2 e).1
    have : 0 < C.a e := by omega
    exact_mod_cast this
  · have := (σ e).isLt
    exact_mod_cast (show (σ e : ℕ) + 1 ≤ C.t by omega)
  · have := k.isLt
    exact_mod_cast (show (k : ℕ) + 3 ≤ C.t by omega)

variable (hC : C.Valid) (ht : 2 ≤ C.t) (hσ : C.IsSolution σ)
include hC ht hσ

lemma slot0_spec : ∀ X, ∀ p ∈ pcs C σ 0 X,
    (C.b : ℝ) * slot0 C σ X ≤ p.1 ∧ p.2 ≤ (C.b : ℝ) * slot0 C σ X + C.b := by
  obtain ⟨hB, ht', ha, hσt, hk, hc2, hc1⟩ := facts C σ hC ht
  intro X p hp
  rcases X with e | _ | k | _ | _ | _ <;> simp [pcs] at hp <;> subst hp <;> simp only [slot0] <;>
    push_cast [hc2, hc1]
  · have := off_nonneg C σ e; have := off_add_le_B C σ hσ e; unfold st; constructor <;> linarith
  · constructor <;> linarith
  · constructor <;> linarith
  · constructor <;> linarith

lemma slot1_spec : ∀ X, ∀ p ∈ pcs C σ 1 X,
    (2 * C.b : ℝ) * slot1 C X ≤ p.1 ∧ p.2 ≤ (2 * C.b : ℝ) * slot1 C X + 2 * C.b := by
  obtain ⟨hB, ht', ha, hσt, hk, hc2, hc1⟩ := facts C σ hC ht
  intro X p hp
  rcases X with e | _ | k | _ | _ | _ <;> simp [pcs] at hp <;> subst hp <;> simp only [slot1] <;>
    push_cast [hc2, hc1]
  · constructor <;> linarith
  · constructor <;> linarith
  · constructor <;> linarith

lemma slot2_spec : ∀ X, ∀ p ∈ pcs C σ 2 X,
    (C.b : ℝ) * slot2 C σ X ≤ p.1 ∧ p.2 ≤ (C.b : ℝ) * slot2 C σ X + C.b := by
  obtain ⟨hB, ht', ha, hσt, hk, hc2, hc1⟩ := facts C σ hC ht
  intro X p hp
  rcases X with e | _ | k | _ | _ | _ <;> simp [pcs] at hp <;> subst hp <;> simp only [slot2] <;>
    push_cast [hc2, hc1]
  · have := off_nonneg C σ e; have := off_add_le_B C σ hσ e; unfold st; constructor <;> linarith
  · constructor <;> linarith
  · constructor <;> linarith
  · constructor <;> linarith

lemma disj0 : ∀ X X' p p', p ∈ pcs C σ 0 X → p' ∈ pcs C σ 0 X' → (X, p) ≠ (X', p') →
    p.2 ≤ p'.1 ∨ p'.2 ≤ p.1 := by
  obtain ⟨hB, ht', ha, hσt, hk, hc2, hc1⟩ := facts C σ hC ht
  intro X X' p p' hp hp' hne
  by_cases hXX : X = X'
  · subst hXX; exact absurd (by rw [pcs_single C σ 0 X p p' hp hp']) hne
  by_cases hn : slot0 C σ X = slot0 C σ X'
  · rcases X with e | _ | k | _ | _ | _ <;> rcases X' with e' | _ | k' | _ | _ | _ <;>
      simp [pcs] at hp hp' <;>
      simp only [slot0, FSJob.elem.injEq, FSJob.middle.injEq, Fin.ext_iff] at hn hXX <;>
      first
        | exact absurd trivial hXX
        | omega
        | (have := k.isLt; omega)
        | (have := k'.isLt; omega)
        | (subst hp hp'; exact elem_disj C σ (by omega) hXX)
  · obtain ⟨a1, a2⟩ := slot0_spec C σ hC ht hσ X p hp
    obtain ⟨b1, b2⟩ := slot0_spec C σ hC ht hσ X' p' hp'
    exact sep hB hn a1 a2 b1 b2

lemma disj1 : ∀ X X' p p', p ∈ pcs C σ 1 X → p' ∈ pcs C σ 1 X' → (X, p) ≠ (X', p') →
    p.2 ≤ p'.1 ∨ p'.2 ≤ p.1 := by
  obtain ⟨hB, ht', ha, hσt, hk, hc2, hc1⟩ := facts C σ hC ht
  intro X X' p p' hp hp' hne
  by_cases hXX : X = X'
  · subst hXX; exact absurd (by rw [pcs_single C σ 1 X p p' hp hp']) hne
  by_cases hn : slot1 C X = slot1 C X'
  · rcases X with e | _ | k | _ | _ | _ <;> rcases X' with e' | _ | k' | _ | _ | _ <;>
      simp [pcs] at hp hp' <;>
      simp only [slot1, FSJob.elem.injEq, FSJob.middle.injEq, Fin.ext_iff] at hn hXX <;>
      first
        | exact absurd trivial hXX
        | omega
        | (have := k.isLt; omega)
        | (have := k'.isLt; omega)
  · obtain ⟨a1, a2⟩ := slot1_spec C σ hC ht hσ X p hp
    obtain ⟨b1, b2⟩ := slot1_spec C σ hC ht hσ X' p' hp'
    exact sep (by linarith) hn a1 a2 b1 b2

lemma disj2 : ∀ X X' p p', p ∈ pcs C σ 2 X → p' ∈ pcs C σ 2 X' → (X, p) ≠ (X', p') →
    p.2 ≤ p'.1 ∨ p'.2 ≤ p.1 := by
  obtain ⟨hB, ht', ha, hσt, hk, hc2, hc1⟩ := facts C σ hC ht
  intro X X' p p' hp hp' hne
  by_cases hXX : X = X'
  · subst hXX; exact absurd (by rw [pcs_single C σ 2 X p p' hp hp']) hne
  by_cases hn : slot2 C σ X = slot2 C σ X'
  · rcases X with e | _ | k | _ | _ | _ <;> rcases X' with e' | _ | k' | _ | _ | _ <;>
      simp [pcs] at hp hp' <;>
      simp only [slot2, FSJob.elem.injEq, FSJob.middle.injEq, Fin.ext_iff] at hn hXX <;>
      first
        | exact absurd trivial hXX
        | omega
        | (subst hp hp'
           have hh := elem_disj C σ (by omega) hXX
           rcases hh with h | h
           · exact Or.inl (by simp only; linarith)
           · exact Or.inr (by simp only; linarith))
  · obtain ⟨a1, a2⟩ := slot2_spec C σ hC ht hσ X p hp
    obtain ⟨b1, b2⟩ := slot2_spec C σ hC ht hσ X' p' hp'
    exact sep hB hn a1 a2 b1 b2

lemma prec : ∀ (X : FSJob C.t) (j j' : Fin 3), j < j' →
    ∀ p ∈ pcs C σ j X, ∀ p' ∈ pcs C σ j' X, p.2 ≤ p'.1 := by
  obtain ⟨hB, ht', ha, hσt, hk, hc2, hc1⟩ := facts C σ hC ht
  intro X j j' hjj p hp p' hp'
  fin_cases j <;> fin_cases j' <;> (try exact absurd hjj (by decide)) <;>
    rcases X with e | _ | k | _ | _ | _ <;> simp [pcs] at hp hp' <;> subst hp hp' <;>
    dsimp only <;>
    first
      | linarith
      | linarith [off_add_le_B C σ hσ e, off_nonneg C σ e]

lemma start_nn : ∀ (j : Fin 3) X, ∀ p ∈ pcs C σ j X, 0 ≤ p.1 := by
  obtain ⟨hB, ht', ha, hσt, hk, hc2, hc1⟩ := facts C σ hC ht
  have h2B := mul_le_mul_of_nonneg_right ht' hB.le
  have hst : ∀ e, 0 ≤ st C σ e := fun e => add_nonneg (by positivity) (off_nonneg C σ e)
  intro j X p hp
  rcases X with e | _ | k | _ | _ | _ <;> fin_cases j <;> simp [pcs] at hp <;> subst hp <;>
    dsimp only <;>
    first
      | positivity
      | linarith
      | linarith [hst e]

lemma lt_end : ∀ (j : Fin 3) X, ∀ p ∈ pcs C σ j X, p.1 < p.2 := by
  obtain ⟨hB, ht', ha, hσt, hk, hc2, hc1⟩ := facts C σ hC ht
  intro j X p hp
  rcases X with e | _ | k | _ | _ | _ <;> fin_cases j <;> simp [pcs] at hp <;> subst hp <;>
    dsimp only <;>
    first
      | linarith
      | linarith [ha e]

lemma ends_le' : ∀ (j : Fin 3) X, ∀ p ∈ pcs C σ j X, p.2 ≤ tau C := by
  obtain ⟨hB, ht', ha, hσt, hk, hc2, hc1⟩ := facts C σ hC ht
  intro j X p hp
  unfold tau
  rcases X with e | _ | k | _ | _ | _ <;> fin_cases j <;> simp [pcs] at hp <;> subst hp <;>
    dsimp only
  · have := off_add_le_B C σ hσ e
    have := mul_le_mul_of_nonneg_right (hσt e) hB.le
    unfold st; linarith
  · have := off_add_le_B C σ hσ e
    have := mul_le_mul_of_nonneg_right (hσt e) hB.le
    unfold st; linarith
  · have := mul_le_mul_of_nonneg_right ht' hB.le; linarith
  · have := mul_le_mul_of_nonneg_right ht' hB.le; linarith
  · have := mul_le_mul_of_nonneg_right (hk k) hB.le; linarith
  · have := mul_le_mul_of_nonneg_right (hk k) hB.le; linarith
  · have := mul_le_mul_of_nonneg_right (hk k) hB.le; linarith
  · have := mul_le_mul_of_nonneg_right ht' hB.le; linarith
  · have := mul_le_mul_of_nonneg_right ht' hB.le; linarith
  · have := mul_le_mul_of_nonneg_right ht' hB.le; linarith
  · have := mul_le_mul_of_nonneg_right ht' hB.le; linarith

lemma len : ∀ (j : Fin 3) X, ∑ p ∈ pcs C σ j X, (p.2 - p.1) = (FS C).t j X := by
  intro j X
  rcases X with e | _ | k | _ | _ | _ <;> fin_cases j <;> simp [pcs, FS, fsTime] <;> ring

noncomputable def sched : PreemptiveSchedule (FS C) where
  pieces := pcs C σ
  start_nonneg := start_nn C σ hC ht hσ
  start_lt_end := lt_end C σ hC ht hσ
  disjoint := by
    intro j
    fin_cases j
    · exact disj0 C σ hC ht hσ
    · exact disj1 C σ hC ht hσ
    · exact disj2 C σ hC ht hσ
  total_length := len C σ hC ht hσ
  precedence := prec C σ hC ht hσ

lemma sched_finish : (sched C σ hC ht hσ).finishTime ≤ tau C := by
  have hτ : 0 ≤ tau C := by unfold tau; positivity
  unfold PreemptiveSchedule.finishTime
  rw [Finset.fold_max_le]
  refine ⟨hτ, fun i _ => ?_⟩
  unfold PreemptiveSchedule.jobFinish
  rw [Finset.fold_max_le]
  refine ⟨hτ, fun p hp => ?_⟩
  obtain ⟨j, _, hp⟩ := Finset.mem_biUnion.1 hp
  exact ends_le' C σ hC ht hσ j i p hp

end Build2

end TPFAux

open ResourceScheduling.Chain FlowJobShop.ThreePartFlow FlowJobShop.ThreePartFlow.FlowShop in
theorem solution (C : ThreePartition) (hC : C.Valid) (ht : 2 ≤ C.t) :
    ((∃ S : PreemptiveSchedule (FS C), S.finishTime ≤ tau C) ↔ C.HasSolution) ∧
      ∀ j i, (FS C).t j i ≤ 2 * (C.b : ℝ) := by
  refine ⟨⟨fun ⟨S, hS⟩ => TPFAux.only_if C hC ht S hS, fun ⟨σ, hσ⟩ =>
    ⟨TPFAux.sched C σ hC ht hσ, TPFAux.sched_finish C σ hC ht hσ⟩⟩, ?_⟩
  intro j i
  have hb : (0 : ℝ) ≤ C.b := Nat.cast_nonneg _
  rcases i with e | _ | k | _ | _ | _ <;> fin_cases j <;> simp [FS, fsTime] <;>
    first
      | linarith
      | (have h := (hC.2.2 e).2
         have h' : C.a e ≤ 2 * C.b := by omega
         exact_mod_cast h')

