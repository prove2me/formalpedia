-- Prove2me | solution 1 for FlowJobShop.PartitionJob.corollary_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:20:04.136617+00:00
-- url     : https://prove2.me/submissions/c39188c6-5792-4ff9-acfb-22ac30854f09

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionJob_Schedule
import Definitions.Def_FlowJobShop_PartitionJob_JS



namespace FlowJobShop.PartitionJob

open JobShopLTAS.Core

def pjov (s f x y : ℝ) : ℝ := max 0 (min f y - max s x)

theorem pjov_nonneg (s f x y : ℝ) : 0 ≤ pjov s f x y := le_max_left _ _

theorem pjov_le (s f x y : ℝ) (h : s ≤ f) : pjov s f x y ≤ f - s := by
  unfold pjov
  refine max_le (by linarith) ?_
  have := min_le_left f y
  have := le_max_left s x
  linarith

theorem pjov_eq (s f x y : ℝ) (h : s ≤ f) (hx : x ≤ s) (hy : f ≤ y) : pjov s f x y = f - s := by
  unfold pjov
  rw [min_eq_left hy, max_eq_left hx]
  exact max_eq_right (by linarith)

theorem pjov_zero_right (s f x y : ℝ) (hy : y ≤ s) : pjov s f x y = 0 := by
  unfold pjov
  have := min_le_right f y
  have := le_max_left s x
  exact max_eq_left (by linarith)

theorem pjov_zero_left (s f x y : ℝ) (hf : f ≤ x) : pjov s f x y = 0 := by
  unfold pjov
  have := min_le_left f y
  have := le_max_right s x
  exact max_eq_left (by linarith)

theorem pjov_split (s f x z y : ℝ) (h : s ≤ f) (hxz : x ≤ z) (hzy : z ≤ y) :
    pjov s f x z + pjov s f z y = pjov s f x y := by
  unfold pjov
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem pj_disj_sum {ι : Type*} (T : Finset ι) (s f : ι → ℝ) (x y : ℝ)
    (hpos : ∀ u ∈ T, s u < f u)
    (hdisj : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → f u ≤ s v ∨ f v ≤ s u)
    (hx : ∀ u ∈ T, x ≤ s u) (hy : ∀ u ∈ T, f u ≤ y) (hxy : x ≤ y) :
    ∑ u ∈ T, (f u - s u) ≤ y - x := by
  classical
  induction T using Finset.induction_on_max_value s generalizing y with
  | empty => simpa using hxy
  | insert a T haT hmax ih =>
    rw [Finset.sum_insert haT]
    have hxa : x ≤ s a := hx a (Finset.mem_insert_self _ _)
    have hfa : f a ≤ y := hy a (Finset.mem_insert_self _ _)
    have hpa : s a < f a := hpos a (Finset.mem_insert_self _ _)
    have hfu : ∀ u ∈ T, f u ≤ s a := by
      intro u hu
      have hne : u ≠ a := fun e => haT (e ▸ hu)
      rcases hdisj u (Finset.mem_insert_of_mem hu) a (Finset.mem_insert_self _ _) hne with h | h
      · exact h
      · have := hmax u hu
        have := hpos u (Finset.mem_insert_of_mem hu)
        linarith
    have := ih (s a)
      (fun u hu => hpos u (Finset.mem_insert_of_mem hu))
      (fun u hu v hv => hdisj u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv))
      (fun u hu => hx u (Finset.mem_insert_of_mem hu)) hfu hxa
    linarith

theorem pj_pack {ι : Type*} (T : Finset ι) (s f : ι → ℝ) (x y : ℝ)
    (hpos : ∀ u ∈ T, s u < f u)
    (hdisj : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → f u ≤ s v ∨ f v ≤ s u) (hxy : x ≤ y) :
    ∑ u ∈ T, pjov (s u) (f u) x y ≤ y - x := by
  classical
  have h1 : ∑ u ∈ T, pjov (s u) (f u) x y =
      ∑ u ∈ T.filter (fun u => max (s u) x < min (f u) y), (min (f u) y - max (s u) x) := by
    rw [← Finset.sum_filter_of_ne (p := fun u => max (s u) x < min (f u) y)]
    · apply Finset.sum_congr rfl
      intro u hu
      have hu' := (Finset.mem_filter.mp hu).2
      unfold pjov
      exact max_eq_right (by linarith)
    · intro u _ hne
      by_contra h
      push_neg at h
      apply hne
      unfold pjov
      exact max_eq_left (by linarith)
  rw [h1]
  apply pj_disj_sum (T.filter (fun u => max (s u) x < min (f u) y)) (fun u => max (s u) x)
    (fun u => min (f u) y) x y
  · intro u hu; exact (Finset.mem_filter.mp hu).2
  · intro u hu v hv huv
    have hu' := Finset.mem_filter.mp hu
    have hv' := Finset.mem_filter.mp hv
    rcases hdisj u hu'.1 v hv'.1 huv with h | h
    · left
      exact le_trans (min_le_left _ _) (le_trans h (le_max_left _ _))
    · right
      exact le_trans (min_le_left _ _) (le_trans h (le_max_left _ _))
  · intro u _; exact le_max_right _ _
  · intro u _; exact min_le_right _ _
  · exact hxy

section generic
variable {m n : ℕ} {inst : Instance m n} (S : Schedule inst)

theorem pj_completed_succ (j : Fin n) (k : ℕ) :
    S.completed j (k + 1) = (S.pieces.filter (fun q => q.1.1 = j ∧ q.1.2.val = k)).fold max
      (S.completed j k) (fun q => q.2.2) := rfl

theorem pj_completed_le_succ (j : Fin n) (k : ℕ) : S.completed j k ≤ S.completed j (k + 1) := by
  rw [pj_completed_succ, Finset.le_fold_max]
  exact Or.inl le_rfl

theorem pj_completed_mono (j : Fin n) : Monotone (S.completed j) :=
  monotone_nat_of_le_succ (pj_completed_le_succ S j)

theorem pj_completed_nonneg (j : Fin n) (k : ℕ) : 0 ≤ S.completed j k := by
  induction k with
  | zero => simp [Schedule.completed]
  | succ k ih => exact le_trans ih (pj_completed_le_succ S j k)

theorem pj_end_le_completed (j : Fin n) (q : inst.Op × ℝ × ℝ) (hq : q ∈ S.pieces)
    (hj : q.1.1 = j) (k : ℕ) (hk : q.1.2.val < k) : q.2.2 ≤ S.completed j k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : q.1.2.val < k
    · exact le_trans (ih h) (pj_completed_le_succ S j k)
    · have hk' : q.1.2.val = k := by omega
      rw [pj_completed_succ, Finset.le_fold_max]
      right
      exact ⟨q, Finset.mem_filter.mpr ⟨hq, hj, hk'⟩, le_rfl⟩

theorem pj_piece_end_le (τ : ℝ) (hτ : S.FinishedBy τ) (q : inst.Op × ℝ × ℝ) (hq : q ∈ S.pieces) :
    q.2.2 ≤ τ := by
  have h1 := pj_end_le_completed S q.1.1 q hq rfl (q.1.2.val + 1) (Nat.lt_succ_self _)
  have h2 := pj_completed_mono S q.1.1 (Nat.succ_le_of_lt q.1.2.isLt)
  exact le_trans h1 (le_trans h2 (hτ q.1.1))

end generic

section js
variable {n : ℕ} (a : Fin n → ℕ) (S : Schedule (JS a))

theorem pj_mach (o : (JS a).Op) : (JS a).mach o = jsMach o.1 o.2.val := rfl
theorem pj_proc (o : (JS a).Op) : (JS a).proc o = jsTime a o.1 o.2.val := rfl
theorem pj_mu (j : Fin (n + 2)) : (JS a).μ j = if j.val < n then 2 else 3 := rfl

theorem pj_Tnn : 0 ≤ PartitionFlow.T a := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (a i))

theorem pj_piece_facts (hS : S.IsPreemptive) (q : (JS a).Op × ℝ × ℝ) (hq : q ∈ S.pieces) :
    0 ≤ q.2.1 := by
  have h1 := hS.task_order q hq
  exact le_trans (pj_completed_nonneg S _ _) h1

theorem pj_before (hS : S.IsPreemptive) (q q' : (JS a).Op × ℝ × ℝ) (hq : q ∈ S.pieces)
    (hq' : q' ∈ S.pieces) (hj : q.1.1 = q'.1.1) (hk : q.1.2.val < q'.1.2.val) :
    q.2.2 ≤ q'.2.1 := by
  have h1 := pj_end_le_completed S q.1.1 q hq rfl q'.1.2.val hk
  have h2 := hS.task_order q' hq'
  generalize q'.1.2.val = k at *
  rw [← hj] at h2
  exact le_trans h1 h2

open Classical in
noncomputable def pjw (j k : ℕ) (x y : ℝ) : ℝ :=
  ∑ q ∈ S.pieces.filter (fun q => q.1.1.val = j ∧ q.1.2.val = k), pjov q.2.1 q.2.2 x y

theorem pjw_nonneg (j k : ℕ) (x y : ℝ) : 0 ≤ pjw a S j k x y :=
  Finset.sum_nonneg (fun q _ => pjov_nonneg _ _ _ _)

theorem pjw_zero_right (j k : ℕ) (x y : ℝ)
    (h : ∀ q ∈ S.pieces, q.1.1.val = j → q.1.2.val = k → y ≤ q.2.1) : pjw a S j k x y = 0 := by
  unfold pjw
  apply Finset.sum_eq_zero
  intro q hq
  have := Finset.mem_filter.mp hq
  exact pjov_zero_right _ _ _ _ (h q this.1 this.2.1 this.2.2)

theorem pjw_zero_left (j k : ℕ) (x y : ℝ)
    (h : ∀ q ∈ S.pieces, q.1.1.val = j → q.1.2.val = k → q.2.2 ≤ x) : pjw a S j k x y = 0 := by
  unfold pjw
  apply Finset.sum_eq_zero
  intro q hq
  have := Finset.mem_filter.mp hq
  exact pjov_zero_left _ _ _ _ (h q this.1 this.2.1 this.2.2)

theorem pjw_full (hS : S.IsPreemptive) (j k : ℕ) (x y : ℝ)
    (h : ∀ q ∈ S.pieces, q.1.1.val = j → q.1.2.val = k → x ≤ q.2.1 ∧ q.2.2 ≤ y) :
    pjw a S j k x y = ∑ q ∈ S.pieces.filter (fun q => q.1.1.val = j ∧ q.1.2.val = k), (q.2.2 - q.2.1) := by
  unfold pjw
  apply Finset.sum_congr rfl
  intro q hq
  have := Finset.mem_filter.mp hq
  exact pjov_eq _ _ _ _ (hS.pos_length q this.1).le (h q this.1 this.2.1 this.2.2).1
    (h q this.1 this.2.1 this.2.2).2

theorem pjw_le_total (hS : S.IsPreemptive) (j k : ℕ) (x y : ℝ) :
    pjw a S j k x y ≤ ∑ q ∈ S.pieces.filter (fun q => q.1.1.val = j ∧ q.1.2.val = k), (q.2.2 - q.2.1) := by
  unfold pjw
  apply Finset.sum_le_sum
  intro q hq
  have := Finset.mem_filter.mp hq
  exact pjov_le _ _ _ _ (hS.pos_length q this.1).le

theorem pj_op_total (hS : S.IsPreemptive) (J : Fin (n + 2)) (k : ℕ) (hk : k < (JS a).μ J) :
    ∑ q ∈ S.pieces.filter (fun q => q.1.1.val = J.val ∧ q.1.2.val = k), (q.2.2 - q.2.1)
      = jsTime a J k := by
  classical
  have hw := hS.total_length ⟨J, ⟨k, hk⟩⟩
  rw [pj_proc] at hw
  simp only at hw
  rw [← hw]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, ?_⟩
    obtain ⟨⟨j', k'⟩, _⟩ := q
    simp only at h1 h2 ⊢
    have : j' = J := Fin.ext h1
    subst this
    have : k' = ⟨k, hk⟩ := Fin.ext h2
    subst this
    rfl
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_, ?_⟩ <;> rw [h1]

theorem pj_op_zero (J : Fin (n + 2)) (k : ℕ) (hk : (JS a).μ J ≤ k) (x y : ℝ) :
    pjw a S J.val k x y = 0 := by
  unfold pjw
  apply Finset.sum_eq_zero
  intro q hq
  exfalso
  have := Finset.mem_filter.mp hq
  have h1 : q.1.1 = J := Fin.ext this.2.1
  have h2 : q.1.2.val < (JS a).μ q.1.1 := q.1.2.isLt
  have h3 : (JS a).μ q.1.1 = (JS a).μ J := by rw [h1]
  have := this.2.2
  omega

theorem pj_span (hS : S.IsPreemptive) (J : Fin (n + 2)) (k : ℕ) (hk : k < (JS a).μ J)
    (x y : ℝ) (hxy : x ≤ y)
    (hall : ∀ q ∈ S.pieces, q.1.1.val = J.val → q.1.2.val = k → x ≤ q.2.1 ∧ q.2.2 ≤ y) :
    jsTime a J k ≤ y - x := by
  classical
  rw [← pj_op_total a S hS J k hk]
  refine pj_disj_sum (S.pieces.filter _) (fun q => q.2.1) (fun q => q.2.2) x y ?_ ?_ ?_ ?_ hxy
  · intro q hq; exact hS.pos_length q (Finset.mem_filter.mp hq).1
  · intro q hq q' hq' hne
    have h1 := Finset.mem_filter.mp hq
    have h2 := Finset.mem_filter.mp hq'
    apply hS.machine_disjoint q h1.1 q' h2.1 hne
    rw [pj_mach, pj_mach]
    have e2 : q.1.2.val = q'.1.2.val := by rw [h1.2.2, h2.2.2]
    simp only [jsMach, h1.2.1, h2.2.1, e2]
  · intro q hq
    have h1 := Finset.mem_filter.mp hq
    exact (hall q h1.1 h1.2.1 h1.2.2).1
  · intro q hq
    have h1 := Finset.mem_filter.mp hq
    exact (hall q h1.1 h1.2.1 h1.2.2).2

def jm (n j k : ℕ) : Fin 2 :=
  if j < n then (if k = 0 then 1 else 0)
  else if j = n then (if k = 1 then 1 else 0)
  else (if k = 1 then 0 else 1)

theorem pj_jm (j : Fin (n + 2)) (k : ℕ) : jsMach j k = jm n j.val k := rfl

open Classical in
noncomputable def pjwr (r : Fin 2) (x y : ℝ) : ℝ :=
  ∑ q ∈ S.pieces.filter (fun q => jm n q.1.1.val q.1.2.val = r), pjov q.2.1 q.2.2 x y

theorem pjwr_decomp (r : Fin 2) (x y : ℝ) :
    pjwr a S r x y = ∑ j ∈ Finset.range (n + 2), ∑ k ∈ Finset.range 3,
      (if jm n j k = r then pjw a S j k x y else 0) := by
  classical
  unfold pjwr
  rw [Finset.sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (s := S.pieces)
    (t := (Finset.range (n + 2)) ×ˢ (Finset.range 3))
    (g := fun q => (q.1.1.val, q.1.2.val))]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    have hf : S.pieces.filter (fun q => (q.1.1.val, q.1.2.val) = (j, k)) =
        S.pieces.filter (fun q => q.1.1.val = j ∧ q.1.2.val = k) := by
      ext q; simp
    rw [hf]
    unfold pjw
    have : ∀ q ∈ S.pieces.filter (fun q => q.1.1.val = j ∧ q.1.2.val = k),
        (if jm n q.1.1.val q.1.2.val = r then pjov q.2.1 q.2.2 x y else 0) =
        if jm n j k = r then pjov q.2.1 q.2.2 x y else 0 := by
      intro q hq
      have := (Finset.mem_filter.mp hq).2
      rw [this.1, this.2]
    rw [Finset.sum_congr rfl this]
    by_cases h : jm n j k = r
    · simp [h]
    · simp [h]
  · intro q _
    simp only [Finset.mem_product, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · have := q.1.1.isLt; omega
    · have h1 : q.1.2.val < (if q.1.1.val < n then 2 else 3) := q.1.2.isLt
      split_ifs at h1 <;> omega

theorem pjwr0_eval (x y : ℝ) : pjwr a S 0 x y =
    ∑ j ∈ Finset.range n, pjw a S j 1 x y + pjw a S n 0 x y + pjw a S n 2 x y
      + pjw a S (n + 1) 1 x y := by
  rw [pjwr_decomp, Finset.sum_range_succ, Finset.sum_range_succ]
  have h1 : ∀ j ∈ Finset.range n, ∑ k ∈ Finset.range 3,
      (if jm n j k = 0 then pjw a S j k x y else 0) = pjw a S j 1 x y := by
    intro j hj
    have hjn := Finset.mem_range.mp hj
    have h2 : pjw a S j 2 x y = 0 :=
      pj_op_zero a S ⟨j, by omega⟩ 2 (by simp [pj_mu, hjn]) x y
    simp [Finset.sum_range_succ, jm, hjn, h2]
  rw [Finset.sum_congr rfl h1]
  simp [Finset.sum_range_succ, jm]
  ring

theorem pjwr1_eval (x y : ℝ) : pjwr a S 1 x y =
    ∑ j ∈ Finset.range n, pjw a S j 0 x y + pjw a S n 1 x y + pjw a S (n + 1) 0 x y
      + pjw a S (n + 1) 2 x y := by
  rw [pjwr_decomp, Finset.sum_range_succ, Finset.sum_range_succ]
  have h1 : ∀ j ∈ Finset.range n, ∑ k ∈ Finset.range 3,
      (if jm n j k = 1 then pjw a S j k x y else 0) = pjw a S j 0 x y := by
    intro j hj
    have hjn := Finset.mem_range.mp hj
    have h2 : pjw a S j 2 x y = 0 :=
      pj_op_zero a S ⟨j, by omega⟩ 2 (by simp [pj_mu, hjn]) x y
    simp [Finset.sum_range_succ, jm, hjn, h2]
  rw [Finset.sum_congr rfl h1]
  simp [Finset.sum_range_succ, jm]
  ring

theorem pj_pc (hS : S.IsPreemptive) (J : Fin (n + 2)) (k : ℕ) :
    ∀ q ∈ S.pieces, q.1.1.val = J.val → q.1.2.val = k →
      S.completed J k ≤ q.2.1 ∧ q.2.2 ≤ S.completed J (k + 1) := by
  rintro ⟨⟨j', k'⟩, s, f⟩ hq h1 h2
  simp only at h1 h2
  have : j' = J := Fin.ext h1
  subst this
  subst h2
  exact ⟨hS.task_order _ hq, pj_end_le_completed S j' _ hq rfl _ (Nat.lt_succ_self _)⟩

theorem pj_K1 (j k : ℕ) (y : ℝ) (h : 0 < pjw a S j k 0 y) :
    ∃ q ∈ S.pieces, q.1.1.val = j ∧ q.1.2.val = k ∧ q.2.1 < y := by
  by_contra hne
  push_neg at hne
  have := pjw_zero_right a S j k 0 y (fun q hq h1 h2 => hne q hq h1 h2)
  linarith

theorem pj_K2 (j k : ℕ) (x y : ℝ) (h : 0 < pjw a S j k x y) :
    ∃ q ∈ S.pieces, q.1.1.val = j ∧ q.1.2.val = k ∧ x < q.2.2 := by
  by_contra hne
  push_neg at hne
  have := pjw_zero_left a S j k x y (fun q hq h1 h2 => hne q hq h1 h2)
  linarith

theorem pj_small_early (hS : S.IsPreemptive) (i : Fin n) (y : ℝ) :
    (pjw a S i.val 1 0 y ≤ pjw a S i.val 0 0 y) ∧
    (0 < pjw a S i.val 1 0 y → pjw a S i.val 0 0 y = a i) := by
  let J : Fin (n + 2) := ⟨i.val, by omega⟩
  have hmu : (JS a).μ J = 2 := by simp [pj_mu, J, i.isLt]
  have tJ : ∀ k, jsTime a J k = a i := by intro k; simp [jsTime, J, i.isLt]
  have hB : 0 < pjw a S i.val 1 0 y → pjw a S i.val 0 0 y = a i := by
    intro h
    obtain ⟨q, hq, h1, h2, h3⟩ := pj_K1 a S _ _ _ h
    have hfull := pjw_full a S hS i.val 0 0 y (fun q' hq' h1' h2' => by
      refine ⟨pj_piece_facts a S hS q' hq', ?_⟩
      have := pj_before a S hS q' q hq' hq (Fin.ext (by rw [h1', h1])) (by omega)
      linarith)
    rw [hfull]
    exact (pj_op_total a S hS J 0 (by rw [hmu]; omega)).trans (tJ 0)
  refine ⟨?_, hB⟩
  by_cases h : 0 < pjw a S i.val 1 0 y
  · rw [hB h]
    have h1 := pjw_le_total a S hS i.val 1 0 y
    have h2 : ∑ q ∈ S.pieces.filter (fun q => q.1.1.val = i.val ∧ q.1.2.val = 1),
        (q.2.2 - q.2.1) = a i :=
      (pj_op_total a S hS J 1 (by rw [hmu]; omega)).trans (tJ 1)
    rw [h2] at h1
    exact h1
  · push_neg at h
    exact le_trans h (pjw_nonneg a S _ _ _ _)

theorem pj_small_late (hS : S.IsPreemptive) (τ : ℝ) (hF : S.FinishedBy τ) (i : Fin n) (x : ℝ) :
    (pjw a S i.val 0 x τ ≤ pjw a S i.val 1 x τ) ∧
    (0 < pjw a S i.val 0 x τ → pjw a S i.val 1 x τ = a i) := by
  let J : Fin (n + 2) := ⟨i.val, by omega⟩
  have hmu : (JS a).μ J = 2 := by simp [pj_mu, J, i.isLt]
  have tJ : ∀ k, jsTime a J k = a i := by intro k; simp [jsTime, J, i.isLt]
  have hB : 0 < pjw a S i.val 0 x τ → pjw a S i.val 1 x τ = a i := by
    intro h
    obtain ⟨q, hq, h1, h2, h3⟩ := pj_K2 a S _ _ _ _ h
    have hfull := pjw_full a S hS i.val 1 x τ (fun q' hq' h1' h2' => by
      refine ⟨?_, pj_piece_end_le S τ hF q' hq'⟩
      have := pj_before a S hS q q' hq hq' (Fin.ext (by rw [h1, h1'])) (by omega)
      linarith)
    rw [hfull]
    exact (pj_op_total a S hS J 1 (by rw [hmu]; omega)).trans (tJ 1)
  refine ⟨?_, hB⟩
  by_cases h : 0 < pjw a S i.val 0 x τ
  · rw [hB h]
    have h1 := pjw_le_total a S hS i.val 0 x τ
    have h2 : ∑ q ∈ S.pieces.filter (fun q => q.1.1.val = i.val ∧ q.1.2.val = 0),
        (q.2.2 - q.2.1) = a i :=
      (pj_op_total a S hS J 0 (by rw [hmu]; omega)).trans (tJ 0)
    rw [h2] at h1
    exact h1
  · push_neg at h
    exact le_trans h (pjw_nonneg a S _ _ _ _)

theorem pj_small_disj (hS : S.IsPreemptive) (i : Fin n) (c d τ : ℝ) (hcd : c ≤ d)
    (h1 : 0 < pjw a S i.val 1 0 c) (h2 : 0 < pjw a S i.val 0 d τ) : False := by
  obtain ⟨q, hq, e1, e2, e3⟩ := pj_K1 a S _ _ _ h1
  obtain ⟨q', hq', e1', e2', e3'⟩ := pj_K2 a S _ _ _ _ h2
  have := pj_before a S hS q' q hq' hq (Fin.ext (by rw [e1, e1'])) (by omega)
  linarith

theorem pj_tot (hS : S.IsPreemptive) (τ : ℝ) (hF : S.FinishedBy τ) (J : Fin (n + 2)) (k : ℕ)
    (hk : k < (JS a).μ J) : pjw a S J.val k 0 τ = jsTime a J k := by
  have hfull := pjw_full a S hS J.val k 0 τ (fun q hq _ _ =>
    ⟨pj_piece_facts a S hS q hq, pj_piece_end_le S τ hF q hq⟩)
  rw [hfull]
  exact pj_op_total a S hS J k hk

theorem pj_busy_le (hS : S.IsPreemptive) (r : Fin 2) (x y : ℝ) (hxy : x ≤ y) :
    pjwr a S r x y ≤ y - x := by
  classical
  unfold pjwr
  refine pj_pack (S.pieces.filter _) (fun q => q.2.1) (fun q => q.2.2) x y ?_ ?_ hxy
  · intro q hq; exact hS.pos_length q (Finset.mem_filter.mp hq).1
  · intro q hq q' hq' hne
    have h1 := Finset.mem_filter.mp hq
    have h2 := Finset.mem_filter.mp hq'
    apply hS.machine_disjoint q h1.1 q' h2.1 hne
    rw [pj_mach, pj_mach]
    simp only [pj_jm]
    rw [h1.2, h2.2]

theorem pj_busy_split (hS : S.IsPreemptive) (r : Fin 2) (x z y : ℝ) (hxz : x ≤ z) (hzy : z ≤ y) :
    pjwr a S r x z + pjwr a S r z y = pjwr a S r x y := by
  unfold pjwr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  exact pjov_split _ _ _ _ _ (hS.pos_length q (Finset.mem_filter.mp hq).1).le hxz hzy

theorem pj_busy (hS : S.IsPreemptive) (r : Fin 2) (τ : ℝ) (hτ : 0 ≤ τ)
    (htot : pjwr a S r 0 τ = τ) (z : ℝ) (hz0 : 0 ≤ z) (hzτ : z ≤ τ) :
    pjwr a S r 0 z = z ∧ pjwr a S r z τ = τ - z := by
  have h1 := pj_busy_split a S hS r 0 z τ hz0 hzτ
  have h2 := pj_busy_le a S hS r 0 z hz0
  have h3 := pj_busy_le a S hS r z τ hzτ
  constructor <;> linarith

theorem pj_sum_small (hS : S.IsPreemptive) (τ : ℝ) (hF : S.FinishedBy τ) (k : ℕ) (hk : k < 2) :
    ∑ j ∈ Finset.range n, pjw a S j k 0 τ = PartitionFlow.T a := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => pjw a S j k 0 τ) n]
  unfold PartitionFlow.T
  apply Finset.sum_congr rfl
  intro i _
  have := pj_tot a S hS τ hF ⟨i.val, by omega⟩ k (by simp [pj_mu, i.isLt]; omega)
  rw [show pjw a S i.val k 0 τ = pjw a S (⟨i.val, by omega⟩ : Fin (n + 2)).val k 0 τ from rfl, this]
  simp [jsTime, i.isLt]

theorem pj_hard (hS : S.IsPreemptive) (hF : S.FinishedBy (5 * PartitionFlow.T a)) :
    PartitionFlow.HasPartition a := by
  classical
  have hsum1 := pj_sum_small a S hS _ hF 1 (by norm_num)
  have hsum0 := pj_sum_small a S hS _ hF 0 (by norm_num)
  set T := PartitionFlow.T a with hTdef
  have hT0 : 0 ≤ T := pj_Tnn a
  let jn : Fin (n + 2) := ⟨n, by omega⟩
  let jb : Fin (n + 2) := ⟨n + 1, by omega⟩
  have mu3 : (JS a).μ jn = 3 := by simp [pj_mu, jn]
  have mub : (JS a).μ jb = 3 := by simp [pj_mu, jb]
  have tA0 : jsTime a jn 0 = T / 2 := by simp [jsTime, jn, hTdef]
  have tA1 : jsTime a jn 1 = T / 2 := by simp [jsTime, jn, hTdef]
  have tA2 : jsTime a jn 2 = 3 * T := by simp [jsTime, jn, hTdef]
  have tB0 : jsTime a jb 0 = 3 * T := by simp [jsTime, jb, hTdef]
  have tB1 : jsTime a jb 1 = T / 2 := by simp [jsTime, jb, hTdef]
  have tB2 : jsTime a jb 2 = T / 2 := by simp [jsTime, jb, hTdef]
  have hc3 : S.completed jn 3 ≤ 5 * T := by
    have := hF jn
    unfold Schedule.jobFinish at this
    rw [mu3] at this
    exact this
  have hb3 : S.completed jb 3 ≤ 5 * T := by
    have := hF jb
    unfold Schedule.jobFinish at this
    rw [mub] at this
    exact this
  have pcA := pj_pc a S hS jn
  have pcB := pj_pc a S hS jb
  have nn := pj_piece_facts a S hS
  have en := pj_piece_end_le S (5 * T) hF
  have cm := pj_completed_mono S
  have cn := pj_completed_nonneg S
  have c0 : S.completed jn 0 = 0 := by simp [Schedule.completed]
  have d0 : S.completed jb 0 = 0 := by simp [Schedule.completed]
  have mA1 := cm jn (show 1 ≤ 2 by norm_num)
  have mA2 := cm jn (show 2 ≤ 3 by norm_num)
  have mB1 := cm jb (show 1 ≤ 2 by norm_num)
  have mB2 := cm jb (show 2 ≤ 3 by norm_num)
  have nA1 := cn jn 1
  have nB1 := cn jb 1
  -- spans
  have hA0 : T / 2 ≤ S.completed jn 1 := by
    have := pj_span a S hS jn 0 (by rw [mu3]; omega) 0 (S.completed jn 1) nA1
      (fun q hq h1 h2 => ⟨nn q hq, (pcA 0 q hq h1 h2).2⟩)
    rw [tA0] at this; linarith
  have hA1 : T / 2 ≤ S.completed jn 2 - S.completed jn 1 := by
    have := pj_span a S hS jn 1 (by rw [mu3]; omega) (S.completed jn 1) (S.completed jn 2) mA1
      (fun q hq h1 h2 => pcA 1 q hq h1 h2)
    rw [tA1] at this; exact this
  have hA2 : 3 * T ≤ 5 * T - S.completed jn 2 := by
    have := pj_span a S hS jn 2 (by rw [mu3]; omega) (S.completed jn 2) (5 * T)
      (le_trans mA2 hc3)
      (fun q hq h1 h2 => ⟨(pcA 2 q hq h1 h2).1, en q hq⟩)
    rw [tA2] at this; exact this
  have hB0 : 3 * T ≤ S.completed jb 1 := by
    have := pj_span a S hS jb 0 (by rw [mub]; omega) 0 (S.completed jb 1) nB1
      (fun q hq h1 h2 => ⟨nn q hq, (pcB 0 q hq h1 h2).2⟩)
    rw [tB0] at this; linarith
  have hB1 : T / 2 ≤ S.completed jb 2 - S.completed jb 1 := by
    have := pj_span a S hS jb 1 (by rw [mub]; omega) (S.completed jb 1) (S.completed jb 2) mB1
      (fun q hq h1 h2 => pcB 1 q hq h1 h2)
    rw [tB1] at this; exact this
  have hB2 : T / 2 ≤ 5 * T - S.completed jb 2 := by
    have := pj_span a S hS jb 2 (by rw [mub]; omega) (S.completed jb 2) (5 * T)
      (le_trans mB2 hb3)
      (fun q hq h1 h2 => ⟨(pcB 2 q hq h1 h2).1, en q hq⟩)
    rw [tB2] at this; exact this
  -- totals
  have fA0 := pj_tot a S hS (5 * T) hF jn 0 (by rw [mu3]; omega)
  have fA1 := pj_tot a S hS (5 * T) hF jn 1 (by rw [mu3]; omega)
  have fA2 := pj_tot a S hS (5 * T) hF jn 2 (by rw [mu3]; omega)
  have fB0 := pj_tot a S hS (5 * T) hF jb 0 (by rw [mub]; omega)
  have fB1 := pj_tot a S hS (5 * T) hF jb 1 (by rw [mub]; omega)
  have fB2 := pj_tot a S hS (5 * T) hF jb 2 (by rw [mub]; omega)
  rw [tA0] at fA0
  rw [tA1] at fA1
  rw [tA2] at fA2
  rw [tB0] at fB0
  rw [tB1] at fB1
  rw [tB2] at fB2
  have tot0 : pjwr a S 0 0 (5 * T) = 5 * T := by
    rw [pjwr0_eval]
    have e1 : pjw a S n 0 0 (5 * T) = T / 2 := fA0
    have e2 : pjw a S n 2 0 (5 * T) = 3 * T := fA2
    have e3 : pjw a S (n + 1) 1 0 (5 * T) = T / 2 := fB1
    rw [hsum1, e1, e2, e3]; ring
  have tot1 : pjwr a S 1 0 (5 * T) = 5 * T := by
    rw [pjwr1_eval]
    have e1 : pjw a S n 1 0 (5 * T) = T / 2 := fA1
    have e2 : pjw a S (n + 1) 0 0 (5 * T) = 3 * T := fB0
    have e3 : pjw a S (n + 1) 2 0 (5 * T) = T / 2 := fB2
    rw [hsum0, e1, e2, e3]; ring
  have hT5 : 0 ≤ 5 * T := by linarith
  -- early cut c, late cut d
  have hcT : T ≤ S.completed jn 2 := by linarith
  have hc2T : S.completed jn 2 ≤ 2 * T := by linarith
  have hd3T : 3 * T ≤ S.completed jb 1 := hB0
  have hd4T : S.completed jb 1 ≤ 4 * T := by linarith
  have hcd : S.completed jn 2 ≤ S.completed jb 1 := by linarith
  have hc5 : S.completed jn 2 ≤ 5 * T := by linarith
  have hd5 : S.completed jb 1 ≤ 5 * T := by linarith
  have hcnn : 0 ≤ S.completed jn 2 := cn jn 2
  have hdnn : 0 ≤ S.completed jb 1 := nB1
  obtain ⟨bc0, -⟩ := pj_busy a S hS 0 (5 * T) hT5 tot0 _ hcnn hc5
  obtain ⟨bc1, -⟩ := pj_busy a S hS 1 (5 * T) hT5 tot1 _ hcnn hc5
  obtain ⟨-, bd0⟩ := pj_busy a S hS 0 (5 * T) hT5 tot0 _ hdnn hd5
  obtain ⟨-, bd1⟩ := pj_busy a S hS 1 (5 * T) hT5 tot1 _ hdnn hd5
  -- E1
  have E1 : S.completed jn 2 = ∑ j ∈ Finset.range n, pjw a S j 1 0 (S.completed jn 2) + T / 2 := by
    have h := bc0
    rw [pjwr0_eval] at h
    have z1 : pjw a S n 2 0 (S.completed jn 2) = 0 :=
      pjw_zero_right a S n 2 0 _ (fun q hq h1 h2 => (pcA 2 q hq h1 h2).1)
    have z2 : pjw a S (n + 1) 1 0 (S.completed jn 2) = 0 :=
      pjw_zero_right a S (n + 1) 1 0 _ (fun q hq h1 h2 => by
        have := (pcB 1 q hq h1 h2).1; linarith)
    have e1 : pjw a S n 0 0 (S.completed jn 2) = T / 2 := by
      rw [pjw_full a S hS n 0 0 _ (fun q hq h1 h2 => ⟨nn q hq, by
        have := (pcA 0 q hq h1 h2).2; linarith⟩)]
      exact (pj_op_total a S hS jn 0 (by rw [mu3]; omega)).trans tA0
    rw [z1, z2, e1] at h; linarith
  have E2 : S.completed jn 2 = ∑ j ∈ Finset.range n, pjw a S j 0 0 (S.completed jn 2) + T / 2
      + pjw a S (n + 1) 0 0 (S.completed jn 2) := by
    have h := bc1
    rw [pjwr1_eval] at h
    have z2 : pjw a S (n + 1) 2 0 (S.completed jn 2) = 0 :=
      pjw_zero_right a S (n + 1) 2 0 _ (fun q hq h1 h2 => by
        have := (pcB 2 q hq h1 h2).1; linarith)
    have e1 : pjw a S n 1 0 (S.completed jn 2) = T / 2 := by
      rw [pjw_full a S hS n 1 0 _ (fun q hq h1 h2 => ⟨nn q hq, (pcA 1 q hq h1 h2).2⟩)]
      exact (pj_op_total a S hS jn 1 (by rw [mu3]; omega)).trans tA1
    rw [z2, e1] at h; linarith
  -- F2, F1
  have F2 : 5 * T - S.completed jb 1 =
      ∑ j ∈ Finset.range n, pjw a S j 0 (S.completed jb 1) (5 * T) + T / 2 := by
    have h := bd1
    rw [pjwr1_eval] at h
    have z1 : pjw a S n 1 (S.completed jb 1) (5 * T) = 0 :=
      pjw_zero_left a S n 1 _ _ (fun q hq h1 h2 => by
        have := (pcA 1 q hq h1 h2).2; linarith)
    have z2 : pjw a S (n + 1) 0 (S.completed jb 1) (5 * T) = 0 :=
      pjw_zero_left a S (n + 1) 0 _ _ (fun q hq h1 h2 => (pcB 0 q hq h1 h2).2)
    have e1 : pjw a S (n + 1) 2 (S.completed jb 1) (5 * T) = T / 2 := by
      rw [pjw_full a S hS (n + 1) 2 _ _ (fun q hq h1 h2 => ⟨by
        have := (pcB 2 q hq h1 h2).1; linarith, en q hq⟩)]
      exact (pj_op_total a S hS jb 2 (by rw [mub]; omega)).trans tB2
    rw [z1, z2, e1] at h; linarith
  have F1 : 5 * T - S.completed jb 1 = ∑ j ∈ Finset.range n, pjw a S j 1 (S.completed jb 1) (5 * T)
      + pjw a S n 2 (S.completed jb 1) (5 * T) + T / 2 := by
    have h := bd0
    rw [pjwr0_eval] at h
    have z1 : pjw a S n 0 (S.completed jb 1) (5 * T) = 0 :=
      pjw_zero_left a S n 0 _ _ (fun q hq h1 h2 => by
        have := (pcA 0 q hq h1 h2).2; linarith)
    have e1 : pjw a S (n + 1) 1 (S.completed jb 1) (5 * T) = T / 2 := by
      rw [pjw_full a S hS (n + 1) 1 _ _ (fun q hq h1 h2 => ⟨(pcB 1 q hq h1 h2).1, by
        have := (pcB 1 q hq h1 h2).2; linarith⟩)]
      exact (pj_op_total a S hS jb 1 (by rw [mub]; omega)).trans tB1
    rw [z1, e1] at h; linarith
  -- finish with sums over Fin n
  have conv : ∀ k x y, ∑ j ∈ Finset.range n, pjw a S j k x y = ∑ i : Fin n, pjw a S i.val k x y :=
    fun k x y => (Fin.sum_univ_eq_sum_range (fun j => pjw a S j k x y) n).symm
  rw [conv] at E1 E2 F2 F1
  generalize hc : S.completed jn 2 = c at *
  generalize hd : S.completed jb 1 = d at *
  have hB0nn : 0 ≤ pjw a S (n + 1) 0 0 c := pjw_nonneg a S _ _ _ _
  have hA2nn : 0 ≤ pjw a S n 2 d (5 * T) := pjw_nonneg a S _ _ _ _
  -- early side
  have eA : ∀ i ∈ (Finset.univ : Finset (Fin n)), pjw a S i.val 1 0 c ≤ pjw a S i.val 0 0 c :=
    fun i _ => (pj_small_early a S hS i c).1
  have sumA : ∑ i : Fin n, pjw a S i.val 1 0 c ≤ ∑ i : Fin n, pjw a S i.val 0 0 c :=
    Finset.sum_le_sum eA
  have eqA := (Finset.sum_eq_sum_iff_of_le eA).mp (le_antisymm sumA (by linarith))
  -- late side
  have eA' : ∀ i ∈ (Finset.univ : Finset (Fin n)), pjw a S i.val 0 d (5 * T) ≤ pjw a S i.val 1 d (5 * T) :=
    fun i _ => (pj_small_late a S hS (5 * T) hF i d).1
  have sumA' : ∑ i : Fin n, pjw a S i.val 0 d (5 * T) ≤ ∑ i : Fin n, pjw a S i.val 1 d (5 * T) :=
    Finset.sum_le_sum eA'
  have eqA' := (Finset.sum_eq_sum_iff_of_le eA').mp (le_antisymm sumA' (by linarith))
  let u : Finset (Fin n) := Finset.univ.filter (fun i => 0 < pjw a S i.val 1 0 c)
  let u' : Finset (Fin n) := Finset.univ.filter (fun i => 0 < pjw a S i.val 0 d (5 * T))
  have hu : ∑ i ∈ u, (a i : ℝ) = c - T / 2 := by
    have : ∑ i ∈ u, (a i : ℝ) = ∑ i ∈ u, pjw a S i.val 1 0 c := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      rw [eqA i (Finset.mem_univ i)]
      exact ((pj_small_early a S hS i c).2 hi').symm
    rw [this]
    have h2 : ∑ i ∈ u, pjw a S i.val 1 0 c = ∑ i : Fin n, pjw a S i.val 1 0 c := by
      apply Finset.sum_filter_of_ne
      intro i _ hne
      by_contra hn
      apply hne
      push_neg at hn
      exact le_antisymm hn (pjw_nonneg a S _ _ _ _)
    rw [h2]; linarith
  have hu' : ∑ i ∈ u', (a i : ℝ) = 5 * T - d - T / 2 := by
    have : ∑ i ∈ u', (a i : ℝ) = ∑ i ∈ u', pjw a S i.val 0 d (5 * T) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      rw [eqA' i (Finset.mem_univ i)]
      exact ((pj_small_late a S hS (5 * T) hF i d).2 hi').symm
    rw [this]
    have h2 : ∑ i ∈ u', pjw a S i.val 0 d (5 * T) = ∑ i : Fin n, pjw a S i.val 0 d (5 * T) := by
      apply Finset.sum_filter_of_ne
      intro i _ hne
      by_contra hn
      apply hne
      push_neg at hn
      exact le_antisymm hn (pjw_nonneg a S _ _ _ _)
    rw [h2]; linarith
  have hdisj : Disjoint u u' := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    exact pj_small_disj a S hS i c d (5 * T) hcd (Finset.mem_filter.mp h1).2
      (Finset.mem_filter.mp h2).2
  have hle : ∑ i ∈ u ∪ u', (a i : ℝ) ≤ T := by
    rw [hTdef]
    unfold PartitionFlow.T
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => Nat.cast_nonneg _)
  rw [Finset.sum_union hdisj, hu, hu'] at hle
  refine ⟨u, ?_⟩
  have key : (2 : ℝ) * ∑ i ∈ u, (a i : ℝ) = T := by rw [hu]; linarith
  have : ((2 * ∑ i ∈ u, a i : ℕ) : ℝ) = ((∑ i, a i : ℕ) : ℝ) := by
    push_cast
    rw [key, hTdef]
    rfl
  exact_mod_cast this

end js

section constr

variable {n : ℕ} (a : Fin n → ℕ) (u : Finset (Fin n))

noncomputable def pjb (T : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => T / 2
  | 2 => T
  | 3 => 4 * T
  | 4 => 9 * T / 2
  | _ => 5 * T

theorem pjb_mono (T : ℝ) (hT : 0 ≤ T) : Monotone (pjb T) := by
  apply monotone_nat_of_le_succ
  intro z
  match z with
  | 0 => simp [pjb]; linarith
  | 1 => simp [pjb]; linarith
  | 2 => simp [pjb]; linarith
  | 3 => simp [pjb]; linarith
  | 4 => simp [pjb]; linarith
  | z + 5 => simp [pjb]

noncomputable def pjpre (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i ∧ (j ∈ u ↔ i ∈ u)), (a j : ℝ)

theorem pjpre_nonneg (i : Fin n) : 0 ≤ pjpre a u i :=
  Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _)

theorem pj_V_sum (hu : 2 * ∑ i ∈ u, a i = ∑ i, a i) (i : Fin n) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j ∈ u ↔ i ∈ u)), (a j : ℝ) = PartitionFlow.T a / 2 := by
  classical
  have h1 : (2 : ℝ) * ∑ i ∈ u, (a i : ℝ) = PartitionFlow.T a := by
    unfold PartitionFlow.T
    exact_mod_cast hu
  by_cases hi : i ∈ u
  · have : Finset.univ.filter (fun j : Fin n => (j ∈ u ↔ i ∈ u)) = u := by
      ext j; simp [hi]
    rw [this]; linarith
  · have : Finset.univ.filter (fun j : Fin n => (j ∈ u ↔ i ∈ u)) = Finset.univ.filter (fun j => j ∉ u) := by
      ext j; simp [hi]
    rw [this]
    have h2 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n)) (fun j => j ∈ u) (fun j => (a j : ℝ))
    have h3 : Finset.univ.filter (fun j : Fin n => j ∈ u) = u := by ext j; simp
    rw [h3] at h2
    unfold PartitionFlow.T at h1 ⊢
    linarith

theorem pj_pre_add_le (hu : 2 * ∑ i ∈ u, a i = ∑ i, a i) (i : Fin n) :
    pjpre a u i + a i ≤ PartitionFlow.T a / 2 := by
  classical
  rw [← pj_V_sum a u hu i]
  unfold pjpre
  have hn : i ∉ Finset.univ.filter (fun j : Fin n => j < i ∧ (j ∈ u ↔ i ∈ u)) := by simp
  rw [add_comm, ← Finset.sum_insert (f := fun j : Fin n => (a j : ℝ)) hn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨_, h⟩
    · exact Iff.rfl
    · exact h
  · intro j _ _; exact Nat.cast_nonneg _

theorem pj_pre_mono (i i' : Fin n) (hlt : i < i') (hs : (i ∈ u ↔ i' ∈ u)) :
    pjpre a u i + a i ≤ pjpre a u i' := by
  classical
  unfold pjpre
  have hn : i ∉ Finset.univ.filter (fun j : Fin n => j < i ∧ (j ∈ u ↔ i ∈ u)) := by simp
  rw [add_comm, ← Finset.sum_insert (f := fun j : Fin n => (a j : ℝ)) hn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨h1, h2⟩
    · exact ⟨hlt, hs⟩
    · exact ⟨lt_trans h1 hlt, h2.trans hs⟩
  · intro j _ _; exact Nat.cast_nonneg _

open Classical in
noncomputable def pjst (j : Fin (n + 2)) (k : ℕ) : ℝ :=
  if h : j.val < n then
    (if (⟨j.val, h⟩ : Fin n) ∈ u then (if k = 0 then 0 else PartitionFlow.T a / 2)
      else (if k = 0 then 4 * PartitionFlow.T a else 9 * PartitionFlow.T a / 2))
      + pjpre a u ⟨j.val, h⟩
  else if j.val = n then (if k = 0 then 0 else if k = 1 then PartitionFlow.T a / 2 else PartitionFlow.T a)
  else (if k = 0 then PartitionFlow.T a else if k = 1 then 4 * PartitionFlow.T a
    else 9 * PartitionFlow.T a / 2)

open Classical in
noncomputable def pjz (j : Fin (n + 2)) (k : ℕ) : ℕ :=
  if h : j.val < n then
    (if (⟨j.val, h⟩ : Fin n) ∈ u then (if k = 0 then 0 else 1) else (if k = 0 then 3 else 4))
  else if j.val = n then (if k = 0 then 0 else if k = 1 then 1 else 2)
  else (if k = 0 then 2 else if k = 1 then 3 else 4)

theorem pj_zone_bounds (hu : 2 * ∑ i ∈ u, a i = ∑ i, a i) (j : Fin (n + 2)) (k : ℕ)
    (hk : k < (JS a).μ j) :
    pjb (PartitionFlow.T a) (pjz u j k) ≤ pjst a u j k ∧
    pjst a u j k + jsTime a j k ≤ pjb (PartitionFlow.T a) (pjz u j k + 1) := by
  have hT := pj_Tnn a
  rw [pj_mu] at hk
  unfold pjst pjz jsTime
  by_cases h : j.val < n
  · have hk2 : k < 2 := by simpa [h] using hk
    have h1 := pjpre_nonneg a u ⟨j.val, h⟩
    have h2 := pj_pre_add_le a u hu ⟨j.val, h⟩
    by_cases hm : (⟨j.val, h⟩ : Fin n) ∈ u
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · simp [h, hm, pjb] <;> (try constructor) <;> linarith
      · simp [h, hm, pjb] <;> (try constructor) <;> linarith
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · simp [h, hm, pjb] <;> (try constructor) <;> linarith
      · simp [h, hm, pjb] <;> (try constructor) <;> linarith
  · by_cases h' : j.val = n
    · have hk3 : k < 3 := by simpa [h] using hk
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
        simp [h, h', pjb] <;> (try constructor) <;> linarith
    · have hk3 : k < 3 := by simpa [h] using hk
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
        simp [h, h', pjb] <;> (try constructor) <;> linarith

theorem pjz_lt (j : Fin (n + 2)) (k k' : ℕ) (hkk : k < k') (hk' : k' < (JS a).μ j) :
    pjz u j k < pjz u j k' := by
  rw [pj_mu] at hk'
  unfold pjz
  by_cases h : j.val < n
  · have : k' < 2 := by simpa [h] using hk'
    have hk0 : k = 0 := by omega
    have hk1 : k' = 1 := by omega
    subst hk0; subst hk1
    by_cases hm : (⟨j.val, h⟩ : Fin n) ∈ u <;> simp [h, hm]
  · have : k' < 3 := by simpa [h] using hk'
    by_cases h' : j.val = n
    · rcases (by omega : (k = 0 ∧ k' = 1) ∨ (k = 0 ∧ k' = 2) ∨ (k = 1 ∧ k' = 2)) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [h, h']
    · rcases (by omega : (k = 0 ∧ k' = 1) ∨ (k = 0 ∧ k' = 2) ∨ (k = 1 ∧ k' = 2)) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [h, h']

theorem pjz_small (j : Fin (n + 2)) (k : ℕ) (h : j.val < n) :
    pjz u j k = if (⟨j.val, h⟩ : Fin n) ∈ u then (if k = 0 then 0 else 1)
      else (if k = 0 then 3 else 4) := by
  unfold pjz; rw [dif_pos h]

theorem pjz_A (j : Fin (n + 2)) (k : ℕ) (h : ¬ j.val < n) (h' : j.val = n) :
    pjz u j k = if k = 0 then 0 else if k = 1 then 1 else 2 := by
  unfold pjz; rw [dif_neg h, if_pos h']

theorem pjz_B (j : Fin (n + 2)) (k : ℕ) (h : ¬ j.val < n) (h' : ¬ j.val = n) :
    pjz u j k = if k = 0 then 2 else if k = 1 then 3 else 4 := by
  unfold pjz; rw [dif_neg h, if_neg h']

theorem jm_small (j k : ℕ) (h : j < n) : jm n j k = if k = 0 then 1 else 0 := by
  unfold jm; rw [if_pos h]

theorem jm_A (j k : ℕ) (h : ¬ j < n) (h' : j = n) : jm n j k = if k = 1 then 1 else 0 := by
  unfold jm; rw [if_neg h, if_pos h']

theorem jm_B (j k : ℕ) (h : ¬ j < n) (h' : ¬ j = n) : jm n j k = if k = 1 then 0 else 1 := by
  unfold jm; rw [if_neg h, if_neg h']

theorem pj_zone_inj (j j' : Fin (n + 2)) (k k' : ℕ) (hk : k < (JS a).μ j) (hk' : k' < (JS a).μ j')
    (hm : jm n j.val k = jm n j'.val k') (hz : pjz u j k = pjz u j' k') :
    (j = j' ∧ k = k') ∨ ∃ i i' : Fin n, i.val = j.val ∧ i'.val = j'.val ∧ k = k' ∧
      (i ∈ u ↔ i' ∈ u) := by
  have hjl := j.isLt
  have hjl' := j'.isLt
  rw [pj_mu] at hk hk'
  by_cases h1 : j.val < n
  · have hk2 : k < 2 := by simpa [h1] using hk
    clear hk
    by_cases h2 : j'.val < n
    · have hk2' : k' < 2 := by simpa [h2] using hk'
      clear hk'
      right
      refine ⟨⟨j.val, h1⟩, ⟨j'.val, h2⟩, rfl, rfl, ?_, ?_⟩ <;>
      · rw [pjz_small u j k h1, pjz_small u j' k' h2] at hz
        rw [jm_small j.val k h1, jm_small j'.val k' h2] at hm
        split_ifs at hz hm <;> first | omega | tauto | (simp at hm; done) | (exfalso; omega)
    · exfalso
      clear hk'
      rw [pjz_small u j k h1] at hz
      by_cases h2' : j'.val = n
      · rw [pjz_A u j' k' h2 h2'] at hz
        rw [jm_small j.val k h1, jm_A j'.val k' h2 h2'] at hm
        split_ifs at hz hm <;> first | omega | (simp at hm; done) | tauto
      · rw [pjz_B u j' k' h2 h2'] at hz
        rw [jm_small j.val k h1, jm_B j'.val k' h2 h2'] at hm
        split_ifs at hz hm <;> first | omega | (simp at hm; done) | tauto
  · have hk3 : k < 3 := by simpa [h1] using hk
    clear hk
    by_cases h2 : j'.val < n
    · exfalso
      clear hk'
      rw [pjz_small u j' k' h2] at hz
      by_cases h1' : j.val = n
      · rw [pjz_A u j k h1 h1'] at hz
        rw [jm_A j.val k h1 h1', jm_small j'.val k' h2] at hm
        split_ifs at hz hm <;> first | omega | (simp at hm; done) | tauto
      · rw [pjz_B u j k h1 h1'] at hz
        rw [jm_B j.val k h1 h1', jm_small j'.val k' h2] at hm
        split_ifs at hz hm <;> first | omega | (simp at hm; done) | tauto
    · left
      have hk3' : k' < 3 := by simpa [h2] using hk'
      clear hk'
      by_cases h1' : j.val = n <;> by_cases h2' : j'.val = n
      · rw [pjz_A u j k h1 h1', pjz_A u j' k' h2 h2'] at hz
        split_ifs at hz <;> first | exact ⟨Fin.ext (by omega), by omega⟩ | omega
      · rw [pjz_A u j k h1 h1', pjz_B u j' k' h2 h2'] at hz
        rw [jm_A j.val k h1 h1', jm_B j'.val k' h2 h2'] at hm
        split_ifs at hz hm <;> first | omega | (simp at hm; done) | tauto
      · rw [pjz_B u j k h1 h1', pjz_A u j' k' h2 h2'] at hz
        rw [jm_B j.val k h1 h1', jm_A j'.val k' h2 h2'] at hm
        split_ifs at hz hm <;> first | omega | (simp at hm; done) | tauto
      · rw [pjz_B u j k h1 h1', pjz_B u j' k' h2 h2'] at hz
        split_ifs at hz <;> first | exact ⟨Fin.ext (by omega), by omega⟩ | omega

theorem pjb_le (T : ℝ) (hT : 0 ≤ T) (z : ℕ) : pjb T z ≤ 5 * T := by
  match z with
  | 0 => simp [pjb]; linarith
  | 1 => simp [pjb]; linarith
  | 2 => simp [pjb]; linarith
  | 3 => simp [pjb]; linarith
  | 4 => simp [pjb]; linarith
  | z + 5 => simp [pjb]

theorem pjb_nonneg (T : ℝ) (hT : 0 ≤ T) (z : ℕ) : 0 ≤ pjb T z := by
  have := pjb_mono T hT (Nat.zero_le z)
  rwa [show pjb T 0 = 0 from rfl] at this

theorem pj_small_order (hu : 2 * ∑ i ∈ u, a i = ∑ i, a i) (j j' : Fin (n + 2)) (k : ℕ)
    (h1 : j.val < n) (h2 : j'.val < n) (hlt : j.val < j'.val)
    (hiff : ((⟨j.val, h1⟩ : Fin n) ∈ u ↔ (⟨j'.val, h2⟩ : Fin n) ∈ u)) :
    pjst a u j k + jsTime a j k ≤ pjst a u j' k := by
  have hp := pj_pre_mono a u ⟨j.val, h1⟩ ⟨j'.val, h2⟩ (Fin.mk_lt_mk.mpr hlt) hiff
  unfold pjst jsTime
  rw [dif_pos h1, dif_pos h2, dif_pos h1]
  by_cases m : (⟨j.val, h1⟩ : Fin n) ∈ u
  · have m' := hiff.mp m
    simp only [m, m', if_true]
    linarith
  · have m' : ¬ (⟨j'.val, h2⟩ : Fin n) ∈ u := fun x => m (hiff.mpr x)
    simp only [m, m', if_false]
    linarith

theorem pj_op_disj (hu : 2 * ∑ i ∈ u, a i = ∑ i, a i) (o o' : (JS a).Op) (hne : o ≠ o')
    (hm : (JS a).mach o = (JS a).mach o') :
    pjst a u o.1 o.2.val + jsTime a o.1 o.2.val ≤ pjst a u o'.1 o'.2.val ∨
    pjst a u o'.1 o'.2.val + jsTime a o'.1 o'.2.val ≤ pjst a u o.1 o.2.val := by
  have hT := pj_Tnn a
  have B := pj_zone_bounds a u hu o.1 o.2.val o.2.isLt
  have B' := pj_zone_bounds a u hu o'.1 o'.2.val o'.2.isLt
  rcases lt_trichotomy (pjz u o.1 o.2.val) (pjz u o'.1 o'.2.val) with hlt | heq | hgt
  · left
    have := pjb_mono _ hT (Nat.succ_le_of_lt hlt)
    linarith [B.2, B'.1]
  · have hm' : jm n o.1.val o.2.val = jm n o'.1.val o'.2.val := hm
    rcases pj_zone_inj a u o.1 o'.1 o.2.val o'.2.val o.2.isLt o'.2.isLt hm' heq with
      ⟨hj, hk⟩ | ⟨i, i', hi, hi', hk, hiff⟩
    · exfalso
      apply hne
      obtain ⟨j, k⟩ := o
      obtain ⟨j', k'⟩ := o'
      simp only at hj hk
      subst hj
      have : k = k' := Fin.ext hk
      subst this
      rfl
    · have h1 : o.1.val < n := by rw [← hi]; exact i.isLt
      have h2 : o'.1.val < n := by rw [← hi']; exact i'.isLt
      have hie : (⟨o.1.val, h1⟩ : Fin n) = i := Fin.ext hi.symm
      have hie' : (⟨o'.1.val, h2⟩ : Fin n) = i' := Fin.ext hi'.symm
      have hiff' : ((⟨o.1.val, h1⟩ : Fin n) ∈ u ↔ (⟨o'.1.val, h2⟩ : Fin n) ∈ u) := by
        rw [hie, hie']; exact hiff
      have hne' : o.1.val ≠ o'.1.val := by
        intro hv
        apply hne
        obtain ⟨j, k⟩ := o
        obtain ⟨j', k'⟩ := o'
        simp only at hv hk
        have : j = j' := Fin.ext hv
        subst this
        have : k = k' := Fin.ext hk
        subst this
        rfl
      rcases lt_or_gt_of_ne hne' with hl | hl
      · left
        rw [← hk]
        exact pj_small_order a u hu o.1 o'.1 o.2.val h1 h2 hl hiff'
      · right
        rw [hk]
        exact pj_small_order a u hu o'.1 o.1 o'.2.val h2 h1 hl hiff'.symm
  · right
    have := pjb_mono _ hT (Nat.succ_le_of_lt hgt)
    linarith [B.1, B'.2]

open Classical in
noncomputable def pjSched : Schedule (JS a) where
  pieces := (Finset.univ.filter (fun o : (JS a).Op => 0 < (JS a).proc o)).image
    (fun o => (o, pjst a u o.1 o.2.val, pjst a u o.1 o.2.val + (JS a).proc o))

theorem pj_mem_pieces (q : (JS a).Op × ℝ × ℝ) :
    q ∈ (pjSched a u).pieces ↔ ∃ o : (JS a).Op, 0 < (JS a).proc o ∧
      q = (o, pjst a u o.1 o.2.val, pjst a u o.1 o.2.val + (JS a).proc o) := by
  classical
  unfold pjSched
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨o, h, rfl⟩; exact ⟨o, h, rfl⟩
  · rintro ⟨o, h, rfl⟩; exact ⟨o, h, rfl⟩

theorem pj_completed_le {m n' : ℕ} {inst : Instance m n'} (S : Schedule inst) (x : ℝ) (hx : 0 ≤ x)
    (j : Fin n') (k : ℕ)
    (h : ∀ q ∈ S.pieces, q.1.1 = j → q.1.2.val < k → q.2.2 ≤ x) : S.completed j k ≤ x := by
  induction k with
  | zero => simpa [Schedule.completed] using hx
  | succ k ih =>
    rw [pj_completed_succ, Finset.fold_max_le]
    refine ⟨ih (fun q hq h1 h2 => h q hq h1 (by omega)), ?_⟩
    intro q hq
    have := Finset.mem_filter.mp hq
    exact h q this.1 this.2.1 (by omega)

theorem pj_sched_preemptive (hu : 2 * ∑ i ∈ u, a i = ∑ i, a i) :
    (pjSched a u).IsPreemptive := by
  have hT := pj_Tnn a
  constructor
  · intro q hq
    obtain ⟨o, ho, rfl⟩ := (pj_mem_pieces a u q).mp hq
    simp only
    linarith
  · intro q hq
    obtain ⟨o, ho, rfl⟩ := (pj_mem_pieces a u q).mp hq
    simp only
    have B := pj_zone_bounds a u hu o.1 o.2.val o.2.isLt
    have hb0 := pjb_nonneg _ hT (pjz u o.1 o.2.val)
    apply pj_completed_le _ _ (by linarith)
    intro q' hq' h1 h2
    obtain ⟨o', ho', rfl⟩ := (pj_mem_pieces a u q').mp hq'
    simp only at h1 h2 ⊢
    have hz := pjz_lt a u o.1 o'.2.val o.2.val h2 o.2.isLt
    have B' := pj_zone_bounds a u hu o.1 o'.2.val (by rw [← h1]; exact o'.2.isLt)
    have := pjb_mono _ hT (Nat.succ_le_of_lt hz)
    simp only [pj_proc]
    have e1 : pjst a u o'.1 o'.2.val = pjst a u o.1 o'.2.val :=
      congrArg (fun j => pjst a u j o'.2.val) h1
    have e2 : jsTime a o'.1 o'.2.val = jsTime a o.1 o'.2.val :=
      congrArg (fun j => jsTime a j o'.2.val) h1
    linarith [B.1, B'.2]
  · intro q hq q' hq' hne hm
    obtain ⟨o, ho, rfl⟩ := (pj_mem_pieces a u q).mp hq
    obtain ⟨o', ho', rfl⟩ := (pj_mem_pieces a u q').mp hq'
    have hoo : o ≠ o' := by
      intro e; apply hne; rw [e]
    simp only
    have := pj_op_disj a u hu o o' hoo hm
    exact this
  · intro o
    classical
    by_cases ho : 0 < (JS a).proc o
    · have : (pjSched a u).pieces.filter (fun q => q.1 = o) =
          {(o, pjst a u o.1 o.2.val, pjst a u o.1 o.2.val + (JS a).proc o)} := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hq, rfl⟩
          obtain ⟨o', ho', rfl⟩ := (pj_mem_pieces a u q).mp hq
          rfl
        · rintro rfl
          exact ⟨(pj_mem_pieces a u _).mpr ⟨o, ho, rfl⟩, rfl⟩
      rw [this, Finset.sum_singleton]
      simp
    · have hz : (JS a).proc o = 0 := le_antisymm (not_lt.mp ho) (by
        have := (JS a).p_nonneg o.1 o.2
        exact this)
      have : (pjSched a u).pieces.filter (fun q => q.1 = o) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro q hq hqo
        obtain ⟨o', ho', rfl⟩ := (pj_mem_pieces a u q).mp hq
        simp only at hqo
        subst hqo
        exact absurd ho' ho
      rw [this, hz]; simp

theorem pj_sched_nonpre (hu : 2 * ∑ i ∈ u, a i = ∑ i, a i) :
    (pjSched a u).IsNonPreemptive := by
  refine ⟨pj_sched_preemptive a u hu, ?_⟩
  intro q hq q' hq' h
  obtain ⟨o, ho, rfl⟩ := (pj_mem_pieces a u q).mp hq
  obtain ⟨o', ho', rfl⟩ := (pj_mem_pieces a u q').mp hq'
  simp only at h
  subst h
  rfl

theorem pj_sched_finish (hu : 2 * ∑ i ∈ u, a i = ∑ i, a i) :
    (pjSched a u).FinishedBy (5 * PartitionFlow.T a) := by
  have hT := pj_Tnn a
  intro j
  unfold Schedule.jobFinish
  apply pj_completed_le _ _ (by linarith)
  intro q hq _ _
  obtain ⟨o, ho, rfl⟩ := (pj_mem_pieces a u q).mp hq
  simp only
  have B := pj_zone_bounds a u hu o.1 o.2.val o.2.isLt
  have := pjb_le _ hT (pjz u o.1 o.2.val + 1)
  simp only [pj_proc]
  linarith [B.2]

theorem pj_forward (h : PartitionFlow.HasPartition a) :
    ∃ S : Schedule (JS a), S.IsNonPreemptive ∧ S.FinishedBy (5 * PartitionFlow.T a) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨pjSched a u, pj_sched_nonpre a u hu, pj_sched_finish a u hu⟩

theorem pj_main (a : Fin n → ℕ) :
    ((∃ S : Schedule (JS a), S.IsPreemptive ∧ S.FinishedBy (5 * PartitionFlow.T a)) ↔
      PartitionFlow.HasPartition a) ∧
    ((∃ S : Schedule (JS a), S.IsNonPreemptive ∧ S.FinishedBy (5 * PartitionFlow.T a)) ↔
      PartitionFlow.HasPartition a) := by
  constructor
  · constructor
    · rintro ⟨S, hS, hF⟩
      exact pj_hard a S hS hF
    · intro h
      obtain ⟨S, h1, h2⟩ := pj_forward a h
      exact ⟨S, h1.1, h2⟩
  · constructor
    · rintro ⟨S, hS, hF⟩
      exact pj_hard a S hS.1 hF
    · exact pj_forward a

end constr

end FlowJobShop.PartitionJob

open FlowJobShop.PartitionJob


theorem solution {n : ℕ} (a : Fin n → ℕ) :
    (∃ S : Schedule (JS a), S.IsNonPreemptive ∧ S.FinishedBy (5 * FlowJobShop.PartitionFlow.T a)) ↔ FlowJobShop.PartitionFlow.HasPartition a := by
  exact (pj_main a).2
