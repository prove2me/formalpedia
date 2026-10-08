-- Prove2me | solution 1 for FlowJobShop.ThreePartJob.lemma_7_preemptive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:49:01.130092+00:00
-- url     : https://prove2.me/submissions/34942edf-e2b0-4923-a7e5-03febb5b6db4

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Schedules



namespace FlowJobShop.ThreePartJob

open ResourceScheduling.Chain

theorem fj_mu_small (C : ThreePartition) (j : Fin (3 * C.t + 1)) (h : j.val < 3 * C.t) :
    (reductionInstance C).μ j = 2 := by simp [reductionInstance, h]

theorem fj_mu_long (C : ThreePartition) (j : Fin (3 * C.t + 1)) (h : ¬ j.val < 3 * C.t) :
    (reductionInstance C).μ j = 2 * C.t := by simp [reductionInstance, h]

theorem fj_mach_small (C : ThreePartition) (j : Fin (3 * C.t + 1)) (h : j.val < 3 * C.t)
    (i : Fin ((reductionInstance C).μ j)) :
    (reductionInstance C).mach ⟨j, i⟩ = if i.val = 0 then 0 else 1 := by
  simp [JobShopLTAS.Core.Instance.mach, reductionInstance, h]

theorem fj_mach_long (C : ThreePartition) (j : Fin (3 * C.t + 1)) (h : ¬ j.val < 3 * C.t)
    (i : Fin ((reductionInstance C).μ j)) :
    (reductionInstance C).mach ⟨j, i⟩ = if i.val % 2 = 0 then 1 else 0 := by
  simp [JobShopLTAS.Core.Instance.mach, reductionInstance, h]

/-- length of an operation, as a natural number -/
def fjLn (C : ThreePartition) (o : (reductionInstance C).Op) : ℕ :=
  if h : o.1.val < 3 * C.t then C.a ⟨o.1.val, h⟩ else C.b

theorem fj_proc (C : ThreePartition) (o : (reductionInstance C).Op) :
    (reductionInstance C).proc o = (fjLn C o : ℝ) := by
  obtain ⟨j, i⟩ := o
  by_cases h : j.val < 3 * C.t
  · simp [JobShopLTAS.Core.Instance.proc, reductionInstance, fjLn, h]
  · simp [JobShopLTAS.Core.Instance.proc, reductionInstance, fjLn, h]

theorem fj_mach_long_op (C : ThreePartition) (o : (reductionInstance C).Op)
    (h : o.1.val = 3 * C.t) :
    (reductionInstance C).mach o = if o.2.val % 2 = 0 then 1 else 0 := by
  obtain ⟨j, i⟩ := o
  exact fj_mach_long C j (by simp at h; omega) i

theorem fj_mach_small_op (C : ThreePartition) (o : (reductionInstance C).Op)
    (h : o.1.val < 3 * C.t) :
    (reductionInstance C).mach o = if o.2.val = 0 then 0 else 1 := by
  obtain ⟨j, i⟩ := o
  exact fj_mach_small C j h i

theorem fj_disj_sum {ι : Type*} (T : Finset ι) (s f : ι → ℝ) (x y : ℝ)
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

/-- pieces of operation `n` of the long job -/
def fjLong (C : ThreePartition) (S : PreemptiveSchedule (reductionInstance C)) (n : ℕ) :
    Finset (Fin S.pieceCount) :=
  Finset.univ.filter (fun u => (S.op u).1.val = 3 * C.t ∧ (S.op u).2.val = n)

theorem fj_long_work (C : ThreePartition) (S : PreemptiveSchedule (reductionInstance C))
    (n : ℕ) (hn : n < 2 * C.t) :
    ∑ u ∈ fjLong C S n, (S.finish u - S.start u) = C.b := by
  have hL : ¬ (3 * C.t < 3 * C.t) := lt_irrefl _
  let L : Fin (3 * C.t + 1) := ⟨3 * C.t, by omega⟩
  have hmu : (reductionInstance C).μ L = 2 * C.t := fj_mu_long C L hL
  let o : (reductionInstance C).Op := ⟨L, ⟨n, by rw [hmu]; exact hn⟩⟩
  have hw := S.work o
  have heq : fjLong C S n = Finset.univ.filter (fun u => S.op u = o) := by
    ext u
    simp only [fjLong, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      rcases hu : S.op u with ⟨j', i'⟩
      rw [hu] at h1 h2
      simp only at h1 h2
      have hj : j' = L := Fin.ext h1
      subst hj
      have : i' = ⟨n, by rw [hmu]; exact hn⟩ := Fin.ext h2
      subst this
      rfl
    · intro h
      rw [h]; exact ⟨rfl, rfl⟩
  rw [heq, hw, fj_proc]
  simp [o, fjLn, L]

theorem fj_long_mach (C : ThreePartition) (S : PreemptiveSchedule (reductionInstance C))
    (u v : Fin S.pieceCount) (hu : (S.op u).1.val = 3 * C.t) (hv : (S.op v).1.val = 3 * C.t)
    (h : (S.op u).2.val % 2 = (S.op v).2.val % 2) :
    (reductionInstance C).mach (S.op u) = (reductionInstance C).mach (S.op v) := by
  rw [fj_mach_long_op C _ hu, fj_mach_long_op C _ hv, h]

theorem fj_long_nonempty (C : ThreePartition) (S : PreemptiveSchedule (reductionInstance C))
    (hv : C.Valid) (n : ℕ) (hn : n < 2 * C.t) : (fjLong C S n).Nonempty := by
  apply Finset.nonempty_of_sum_ne_zero (f := fun u => S.finish u - S.start u)
  rw [fj_long_work C S n hn]
  have : (0:ℝ) < C.b := by exact_mod_cast hv.1
  exact this.ne'

theorem fj_long_ge (C : ThreePartition) (hv : C.Valid)
    (S : PreemptiveSchedule (reductionInstance C)) :
    ∀ n, n < 2 * C.t → ∀ u : Fin S.pieceCount, (S.op u).1.val = 3 * C.t → (S.op u).2.val = n →
      (n : ℝ) * C.b ≤ S.start u := by
  intro n
  induction n with
  | zero =>
    intro _ u _ _
    simpa using (S.piece_positive u).1
  | succ n ih =>
    intro hn u hu hun
    have ih' := ih (by omega)
    have hne := fj_long_nonempty C S hv n (by omega)
    obtain ⟨w0, hw0⟩ := hne
    have hprec : ∀ w ∈ fjLong C S n, S.finish w ≤ S.start u := by
      intro w hw
      simp only [fjLong, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      apply S.precedence w u
      · apply Fin.ext; rw [hw.1, hu]
      · rw [hw.2, hun]; omega
    have key := fj_disj_sum (fjLong C S n) S.start S.finish ((n : ℝ) * C.b) (S.start u)
      (fun w _ => (S.piece_positive w).2)
      (by
        intro w hw w' hw' hne
        simp only [fjLong, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
        exact S.machine_disjoint w w' hne (fj_long_mach C S w w' hw.1 hw'.1 (by rw [hw.2, hw'.2])))
      (fun w hw => by
        simp only [fjLong, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        exact ih' w hw.1 hw.2)
      hprec
      (by
        have h1 := hprec w0 hw0
        have h2 := (S.piece_positive w0).2
        simp only [fjLong, Finset.mem_filter, Finset.mem_univ, true_and] at hw0
        have := ih' w0 hw0.1 hw0.2
        linarith)
    rw [fj_long_work C S n (by omega)] at key
    push_cast
    linarith

theorem fj_long_le (C : ThreePartition) (hv : C.Valid)
    (S : PreemptiveSchedule (reductionInstance C)) (hfinish : S.FinishesBy (threshold C)) :
    ∀ m n, n + m + 1 = 2 * C.t → ∀ u : Fin S.pieceCount, (S.op u).1.val = 3 * C.t →
      (S.op u).2.val = n → S.finish u ≤ ((n : ℝ) + 1) * C.b := by
  intro m
  induction m with
  | zero =>
    intro n hn u _ _
    have := hfinish u
    have e : ((n : ℝ) + 1) * C.b = threshold C := by
      unfold threshold
      have : n + 1 = 2 * C.t := by omega
      rw [← this]; push_cast; ring
    linarith
  | succ m ih =>
    intro n hn u hu hun
    have ih' := ih (n + 1) (by omega)
    have hne := fj_long_nonempty C S hv (n + 1) (by omega)
    obtain ⟨w0, hw0⟩ := hne
    have hprec : ∀ w ∈ fjLong C S (n + 1), S.finish u ≤ S.start w := by
      intro w hw
      simp only [fjLong, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      apply S.precedence u w
      · apply Fin.ext; rw [hw.1, hu]
      · rw [hw.2, hun]; omega
    have key := fj_disj_sum (fjLong C S (n + 1)) S.start S.finish (S.finish u)
      ((((n + 1 : ℕ) : ℝ) + 1) * C.b)
      (fun w _ => (S.piece_positive w).2)
      (by
        intro w hw w' hw' hne
        simp only [fjLong, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
        exact S.machine_disjoint w w' hne (fj_long_mach C S w w' hw.1 hw'.1 (by rw [hw.2, hw'.2])))
      hprec
      (fun w hw => by
        simp only [fjLong, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        exact ih' w hw.1 hw.2)
      (by
        have h1 := hprec w0 hw0
        have h2 := (S.piece_positive w0).2
        simp only [fjLong, Finset.mem_filter, Finset.mem_univ, true_and] at hw0
        have := ih' w0 hw0.1 hw0.2
        linarith)
    rw [fj_long_work C S (n + 1) (by omega)] at key
    push_cast at key
    linarith

theorem fj_forced_core (C : ThreePartition) (hvalid : C.Valid)
    (S : PreemptiveSchedule (reductionInstance C))
    (hfinish : S.FinishesBy (threshold C)) :
    ∀ u : Fin S.pieceCount, (S.op u).1.val = 3 * C.t →
      ((S.op u).2.val : ℝ) * C.b ≤ S.start u ∧
        S.finish u ≤ (((S.op u).2.val + 1 : ℕ) : ℝ) * C.b := by
  intro u hu
  have hmu := fj_mu_long C (S.op u).1 (by omega)
  have hi : (S.op u).2.val < 2 * C.t := by
    have := (S.op u).2.isLt
    omega
  refine ⟨fj_long_ge C hvalid S _ hi u hu rfl, ?_⟩
  have := fj_long_le C hvalid S hfinish (2 * C.t - (S.op u).2.val - 1) (S.op u).2.val
    (by omega) u hu rfl
  push_cast
  exact this


/-- processing time of a job, independent of the operation index -/
def fjPrc (C : ThreePartition) (j : Fin (3 * C.t + 1)) : ℝ :=
  if h : j.val < 3 * C.t then (C.a ⟨j.val, h⟩ : ℝ) else (C.b : ℝ)

theorem fj_proc' (C : ThreePartition) (o : (reductionInstance C).Op) :
    (reductionInstance C).proc o = fjPrc C o.1 := by
  rw [fj_proc]
  unfold fjLn fjPrc
  split_ifs <;> simp

open Classical in
theorem fj_sumQ0 (C : ThreePartition) (S : PreemptiveSchedule (reductionInstance C))
    (Q : ℕ → ℕ → Prop) :
    ∑ u ∈ Finset.univ.filter (fun u => Q (S.op u).1.val (S.op u).2.val), (S.finish u - S.start u)
      = ∑ o : (reductionInstance C).Op,
          if Q o.1.val o.2.val then (reductionInstance C).proc o else 0 := by
  rw [Finset.sum_filter, ← Finset.sum_fiberwise Finset.univ S.op]
  refine Finset.sum_congr rfl (fun o _ => ?_)
  have h1 : ∀ u ∈ Finset.univ.filter (fun u => S.op u = o),
      (if Q (S.op u).1.val (S.op u).2.val then (S.finish u - S.start u) else 0)
        = if Q o.1.val o.2.val then (S.finish u - S.start u) else 0 := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [hu]
  rw [Finset.sum_congr rfl h1]
  by_cases hq : Q o.1.val o.2.val
  · simp only [hq, if_true]
    exact S.work o
  · simp [hq]

open Classical in
theorem fj_sumQ (C : ThreePartition) (S : PreemptiveSchedule (reductionInstance C))
    (Q : ℕ → ℕ → Prop) :
    ∑ u ∈ Finset.univ.filter (fun u => Q (S.op u).1.val (S.op u).2.val), (S.finish u - S.start u)
      = ∑ j : Fin (3 * C.t + 1), ∑ i ∈ Finset.range ((reductionInstance C).μ j),
          if Q j.val i then fjPrc C j else 0 := by
  rw [fj_sumQ0]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Fin.sum_univ_eq_sum_range (fun i => if Q j.val i then fjPrc C j else 0)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [fj_proc']

open Classical in
theorem fj_sumQ_eval (C : ThreePartition) (S : PreemptiveSchedule (reductionInstance C))
    (e : ℕ) (he : e < 2) (Dn : ℕ → Prop) (Lp : ℕ → Prop) :
    ∑ u ∈ Finset.univ.filter (fun u =>
        ((S.op u).1.val < 3 * C.t ∧ (S.op u).2.val = e ∧ Dn (S.op u).1.val) ∨
        ((S.op u).1.val = 3 * C.t ∧ Lp (S.op u).2.val)), (S.finish u - S.start u)
      = ∑ j ∈ Finset.univ.filter (fun j : Fin (3 * C.t) => Dn j.val), (C.a j : ℝ)
        + ((Finset.range (2 * C.t)).filter Lp).card * (C.b : ℝ) := by
  have h := fj_sumQ C S (fun j i => (j < 3 * C.t ∧ i = e ∧ Dn j) ∨ (j = 3 * C.t ∧ Lp i))
  refine (Finset.sum_congr (by ext; simp) (fun _ _ => rfl)).trans (h.trans ?_)
  rw [Fin.sum_univ_castSucc]
  congr 1
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : (Fin.castSucc j).val < 3 * C.t := by simp
    rw [fj_mu_small C _ hj]
    have hp : fjPrc C (Fin.castSucc j) = (C.a j : ℝ) := by simp [fjPrc]
    rw [hp]
    have hjl : ¬ (j.val = 3 * C.t) := by have := j.isLt; omega
    have hjl2 : j.val < 3 * C.t := j.isLt
    interval_cases e <;> simp [Finset.sum_range_succ, hjl, hjl2]
  · have hj : ¬ ((Fin.last (3 * C.t)).val < 3 * C.t) := by simp
    rw [fj_mu_long C _ hj]
    have hp : fjPrc C (Fin.last _) = (C.b : ℝ) := by simp [fjPrc]
    rw [hp]
    simp only [Fin.val_last, lt_irrefl, false_and, true_and, false_or]
    rw [← Finset.sum_filter]
    simp

theorem fj_card_up (t k : ℕ) (hk : k < t) :
    ((Finset.range (2 * t)).filter (fun i => i % 2 = 1 ∧ i ≤ 2 * k + 1)).card = k + 1 := by
  have : (Finset.range (2 * t)).filter (fun i => i % 2 = 1 ∧ i ≤ 2 * k + 1)
      = (Finset.range (k + 1)).image (fun m => 2 * m + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨i / 2, by omega, by omega⟩
    · rintro ⟨m, hm, rfl⟩
      omega
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp

theorem fj_card_low (t k : ℕ) (hk : k < t) :
    ((Finset.range (2 * t)).filter (fun i => i % 2 = 0 ∧ 2 * k + 2 ≤ i)).card = t - k - 1 := by
  have : (Finset.range (2 * t)).filter (fun i => i % 2 = 0 ∧ 2 * k + 2 ≤ i)
      = (Finset.range (t - k - 1)).image (fun m => 2 * (k + 1 + m)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨i / 2 - (k + 1), by omega, by omega⟩
    · rintro ⟨m, hm, rfl⟩
      omega
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp

open Classical in
theorem fj_cap (C : ThreePartition) (S : PreemptiveSchedule (reductionInstance C))
    (e : ℕ) (he : e < 2) (Dn Lp : ℕ → Prop) (x y : ℝ) (n : ℕ)
    (hn : ((Finset.range (2 * C.t)).filter Lp).card = n) (hxy : x ≤ y)
    (hx : ∀ u, (((S.op u).1.val < 3 * C.t ∧ (S.op u).2.val = e ∧ Dn (S.op u).1.val) ∨
        ((S.op u).1.val = 3 * C.t ∧ Lp (S.op u).2.val)) → x ≤ S.start u)
    (hy : ∀ u, (((S.op u).1.val < 3 * C.t ∧ (S.op u).2.val = e ∧ Dn (S.op u).1.val) ∨
        ((S.op u).1.val = 3 * C.t ∧ Lp (S.op u).2.val)) → S.finish u ≤ y)
    (hm : ∀ u v, (((S.op u).1.val < 3 * C.t ∧ (S.op u).2.val = e ∧ Dn (S.op u).1.val) ∨
        ((S.op u).1.val = 3 * C.t ∧ Lp (S.op u).2.val)) →
        (((S.op v).1.val < 3 * C.t ∧ (S.op v).2.val = e ∧ Dn (S.op v).1.val) ∨
        ((S.op v).1.val = 3 * C.t ∧ Lp (S.op v).2.val)) →
        (reductionInstance C).mach (S.op u) = (reductionInstance C).mach (S.op v)) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (3 * C.t) => Dn j.val), (C.a j : ℝ)
        + n * (C.b : ℝ) ≤ y - x := by
  rw [← hn, ← fj_sumQ_eval C S e he Dn Lp]
  apply fj_disj_sum _ S.start S.finish x y
  · intro u _; exact (S.piece_positive u).2
  · intro u hu v hv hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact S.machine_disjoint u v hne (hm u v hu hv)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact hx u hu
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact hy u hu
  · exact hxy

/-- op0 of job `j` is finished by `y_k = (2k+2)b` -/
def fjDup (C : ThreePartition) (S : PreemptiveSchedule (reductionInstance C)) (k j : ℕ) : Prop :=
  ∀ u, (S.op u).1.val = j → (S.op u).2.val = 0 → S.finish u ≤ ((2 * k + 2 : ℕ) : ℝ) * C.b

/-- all op1 pieces of job `j` start at or after `y_k` -/
def fjDlow (C : ThreePartition) (S : PreemptiveSchedule (reductionInstance C)) (k j : ℕ) : Prop :=
  ∀ u, (S.op u).1.val = j → (S.op u).2.val = 1 → ((2 * k + 2 : ℕ) : ℝ) * C.b ≤ S.start u

open Classical in
theorem fj_upper (C : ThreePartition) (hv : C.Valid)
    (S : PreemptiveSchedule (reductionInstance C)) (hfin : S.FinishesBy (threshold C))
    (k : ℕ) (hk : k < C.t) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (3 * C.t) => fjDup C S k j.val), (C.a j : ℝ)
      ≤ ((k + 1 : ℕ) : ℝ) * C.b := by
  have hm0 : ∀ u, (((S.op u).1.val < 3 * C.t ∧ (S.op u).2.val = 0 ∧ fjDup C S k (S.op u).1.val) ∨
        ((S.op u).1.val = 3 * C.t ∧ ((S.op u).2.val % 2 = 1 ∧ (S.op u).2.val ≤ 2 * k + 1))) →
        (reductionInstance C).mach (S.op u) = 0 := by
    intro u hu
    rcases hu with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · rw [fj_mach_small_op C _ h1]; simp [h2]
    · rw [fj_mach_long_op C _ h1]; simp [h2]
  have hc := fj_cap C S 0 (by norm_num) (fjDup C S k) (fun i => i % 2 = 1 ∧ i ≤ 2 * k + 1) 0
    (((2 * k + 2 : ℕ) : ℝ) * C.b) (k + 1) (by convert fj_card_up C.t k hk) (by positivity)
    (fun u _ => (S.piece_positive u).1)
    (by
      intro u hu
      rcases hu with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact h3 u rfl h2
      · have := (fj_forced_core C hv S hfin u h1).2
        refine this.trans ?_
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : (S.op u).2.val + 1 ≤ 2 * k + 2))
          (by positivity))
    (fun u v hu hv => (hm0 u hu).trans (hm0 v hv).symm)
  push_cast at hc ⊢
  linarith

open Classical in
theorem fj_lower (C : ThreePartition) (hv : C.Valid)
    (S : PreemptiveSchedule (reductionInstance C)) (hfin : S.FinishesBy (threshold C))
    (k : ℕ) (hk : k < C.t) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (3 * C.t) => fjDlow C S k j.val), (C.a j : ℝ)
      ≤ ((C.t : ℝ) - k - 1) * C.b := by
  have hm0 : ∀ u, (((S.op u).1.val < 3 * C.t ∧ (S.op u).2.val = 1 ∧ fjDlow C S k (S.op u).1.val) ∨
        ((S.op u).1.val = 3 * C.t ∧ ((S.op u).2.val % 2 = 0 ∧ 2 * k + 2 ≤ (S.op u).2.val))) →
        (reductionInstance C).mach (S.op u) = 1 := by
    intro u hu
    rcases hu with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · rw [fj_mach_small_op C _ h1]; simp [h2]
    · rw [fj_mach_long_op C _ h1]; simp [h2]
  have hb : (0:ℝ) < C.b := by exact_mod_cast hv.1
  have hc := fj_cap C S 1 (by norm_num) (fjDlow C S k) (fun i => i % 2 = 0 ∧ 2 * k + 2 ≤ i)
    (((2 * k + 2 : ℕ) : ℝ) * C.b) (threshold C) (C.t - k - 1)
    (by convert fj_card_low C.t k hk)
    (by
      unfold threshold
      have : 2 * k + 2 ≤ 2 * C.t := by omega
      exact_mod_cast (by nlinarith : (2 * k + 2) * C.b ≤ 2 * C.t * C.b))
    (by
      intro u hu
      rcases hu with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact h3 u rfl h2
      · have := (fj_forced_core C hv S hfin u h1).1
        refine le_trans ?_ this
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast h3) (by positivity))
    (fun u _ => hfin u)
    (fun u v hu hv => (hm0 u hu).trans (hm0 v hv).symm)
  have hcast : ((C.t - k - 1 : ℕ) : ℝ) = (C.t : ℝ) - k - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  rw [hcast] at hc
  unfold threshold at hc
  push_cast at hc
  nlinarith

open Classical in
theorem fj_eq (C : ThreePartition) (hv : C.Valid)
    (S : PreemptiveSchedule (reductionInstance C)) (hfin : S.FinishesBy (threshold C))
    (k : ℕ) (hk : k < C.t) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (3 * C.t) => fjDup C S k j.val), (C.a j : ℝ)
      = ((k + 1 : ℕ) : ℝ) * C.b := by
  have hU := fj_upper C hv S hfin k hk
  have hL := fj_lower C hv S hfin k hk
  have htot : ∑ j : Fin (3 * C.t), (C.a j : ℝ) = C.t * C.b := by
    have := hv.2.1
    exact_mod_cast this
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin (3 * C.t) => fjDlow C S k j.val) (fun j => (C.a j : ℝ))
  have hsub : Finset.univ.filter (fun j : Fin (3 * C.t) => ¬ fjDlow C S k j.val)
      ⊆ Finset.univ.filter (fun j : Fin (3 * C.t) => fjDup C S k j.val) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    unfold fjDlow at hj
    push_neg at hj
    obtain ⟨v, hv1, hv2, hv3⟩ := hj
    intro u hu1 hu2
    have := S.precedence u v (Fin.ext (by rw [hu1, hv1])) (by rw [hu2, hv2]; omega)
    exact (this.trans hv3.le)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => (by positivity : (0:ℝ) ≤ (C.a i : ℝ)))
  push_cast at hU ⊢
  nlinarith

theorem fj_extract (C : ThreePartition) (hv : C.Valid) (D : ℕ → Finset (Fin (3 * C.t)))
    (hsum : ∀ k, k < C.t → ∑ j ∈ D k, C.a j = (k + 1) * C.b)
    (hmono : ∀ k k', k ≤ k' → k' < C.t → D k ⊆ D k') : C.HasSolution := by
  classical
  by_cases ht : C.t = 0
  · exact ⟨fun j => absurd j.isLt (by omega), fun i => absurd i.isLt (by omega)⟩
  have hapos : ∀ j, 0 < C.a j := by
    intro j
    have := hv.2.2 j
    have := hv.1
    omega
  have hall : ∀ j : Fin (3 * C.t), ∃ k, k < C.t ∧ j ∈ D k := by
    intro j
    refine ⟨C.t - 1, by omega, ?_⟩
    by_contra hj
    have h1 := hsum (C.t - 1) (by omega)
    have h2 : ∑ x ∈ D (C.t - 1), C.a x < ∑ x, C.a x :=
      Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ j) hj (hapos j)
        (fun _ _ _ => Nat.zero_le _)
    rw [hv.2.1, h1] at h2
    have : C.t - 1 + 1 = C.t := by omega
    rw [this] at h2
    exact lt_irrefl _ h2
  let σ : Fin (3 * C.t) → Fin C.t := fun j =>
    ⟨Nat.find (hall j), (Nat.find_spec (hall j)).1⟩
  have hσ : ∀ (j : Fin (3 * C.t)) (i : Fin C.t), σ j = i ↔
      (j ∈ D i ∧ (i.val = 0 ∨ j ∉ D (i.val - 1))) := by
    intro j i
    have hfind := Nat.find_eq_iff (hall j) (m := i.val)
    constructor
    · intro h
      have h' : Nat.find (hall j) = i.val := congrArg Fin.val h
      rw [hfind] at h'
      refine ⟨h'.1.2, ?_⟩
      by_cases h0 : i.val = 0
      · exact Or.inl h0
      · right
        intro hj
        exact h'.2 (i.val - 1) (by omega) ⟨by omega, hj⟩
    · rintro ⟨h1, h2⟩
      apply Fin.ext
      show Nat.find (hall j) = i.val
      rw [hfind]
      refine ⟨⟨i.isLt, h1⟩, ?_⟩
      intro n hn hn2
      rcases h2 with h2 | h2
      · omega
      · exact h2 (hmono n (i.val - 1) (by omega) (by omega) hn2.2)
  refine ⟨σ, fun i => ?_⟩
  have hfib : Finset.univ.filter (fun j => σ j = i) =
      D i \ (if i.val = 0 then ∅ else D (i.val - 1)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, hσ]
    by_cases h0 : i.val = 0 <;> simp [h0]
  have hsub : (if i.val = 0 then ∅ else D (i.val - 1)) ⊆ D i := by
    by_cases h0 : i.val = 0
    · simp [h0]
    · simp only [h0, if_false]
      exact hmono _ _ (by omega) i.isLt
  have hsb : ∑ j ∈ Finset.univ.filter (fun j => σ j = i), C.a j = C.b := by
    rw [hfib]
    have h1 := Finset.sum_sdiff hsub (f := C.a)
    have h2 := hsum i.val i.isLt
    have h3 : ∑ j ∈ (if i.val = 0 then ∅ else D (i.val - 1)), C.a j = i.val * C.b := by
      by_cases h0 : i.val = 0
      · simp [h0]
      · simp only [h0, if_false]
        rw [hsum (i.val - 1) (by omega)]
        have : i.val - 1 + 1 = i.val := by omega
        rw [this]
    rw [h3, h2] at h1
    nlinarith
  refine ⟨?_, hsb⟩
  set F := Finset.univ.filter (fun j => σ j = i) with hF
  have hne : F.Nonempty := by
    apply Finset.nonempty_of_sum_ne_zero (f := C.a)
    have := hv.1
    rw [hsb]; omega
  have hlt1 : ∑ _j ∈ F, C.b < ∑ j ∈ F, 4 * C.a j :=
    Finset.sum_lt_sum_of_nonempty hne (fun j _ => (hv.2.2 j).1)
  have hlt2 : ∑ j ∈ F, 2 * C.a j < ∑ _j ∈ F, C.b :=
    Finset.sum_lt_sum_of_nonempty hne (fun j _ => (hv.2.2 j).2)
  rw [← Finset.mul_sum, hsb, Finset.sum_const, smul_eq_mul] at hlt1
  rw [← Finset.mul_sum, hsb, Finset.sum_const, smul_eq_mul] at hlt2
  have hb := hv.1
  have c1 : F.card < 4 := by
    by_contra h; push_neg at h; nlinarith
  have c2 : 2 < F.card := by
    by_contra h; push_neg at h; nlinarith
  omega

theorem fj_lemma_7b_core (C : ThreePartition) (hvalid : C.Valid) (hno : ¬ C.HasSolution) :
    ∀ S : PreemptiveSchedule (reductionInstance C),
      ∃ u : Fin S.pieceCount, threshold C < S.finish u := by
  classical
  intro S
  by_contra hcon
  push_neg at hcon
  apply hno
  refine fj_extract C hvalid
    (fun k => Finset.univ.filter (fun j : Fin (3 * C.t) => fjDup C S k j.val)) ?_ ?_
  · intro k hk
    have := fj_eq C hvalid S hcon k hk
    exact_mod_cast this
  · intro k k' hkk' _ j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    intro u h1 h2
    refine (hj u h1 h2).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 2 * k + 2 ≤ 2 * k' + 2))
      (by positivity)

def fjOffs (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t) (j : Fin (3 * C.t)) : ℕ :=
  ∑ j' ∈ Finset.univ.filter (fun j' => j' < j ∧ σ j' = σ j), C.a j'

theorem fj_offs_add_le (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t)
    (hσ : C.IsSolution σ) (j : Fin (3 * C.t)) : fjOffs C σ j + C.a j ≤ C.b := by
  have h1 : j ∉ Finset.univ.filter (fun j' => j' < j ∧ σ j' = σ j) := by simp
  have h2 : insert j (Finset.univ.filter (fun j' => j' < j ∧ σ j' = σ j)) ⊆
      Finset.univ.filter (fun j' => σ j' = σ j) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨_, h⟩ <;> simp [*]
  have := Finset.sum_le_sum_of_subset (f := C.a) h2
  rw [Finset.sum_insert h1] at this
  have h3 := (hσ (σ j)).2
  unfold fjOffs
  omega

theorem fj_offs_mono (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t)
    (j j' : Fin (3 * C.t)) (hlt : j < j') (hs : σ j = σ j') :
    fjOffs C σ j + C.a j ≤ fjOffs C σ j' := by
  have h1 : j ∉ Finset.univ.filter (fun x => x < j ∧ σ x = σ j) := by simp
  have h2 : insert j (Finset.univ.filter (fun x => x < j ∧ σ x = σ j)) ⊆
      Finset.univ.filter (fun x => x < j' ∧ σ x = σ j') := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨h, h'⟩
    · exact ⟨hlt, hs⟩
    · exact ⟨lt_trans h hlt, h'.trans hs⟩
  have := Finset.sum_le_sum_of_subset (f := C.a) h2
  rw [Finset.sum_insert h1] at this
  unfold fjOffs
  omega

/-- start time of an operation (natural number) -/
def fjSt (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t) (o : (reductionInstance C).Op) : ℕ :=
  if h : o.1.val < 3 * C.t then
    (if o.2.val = 0 then 2 * (σ ⟨o.1.val, h⟩).val * C.b + fjOffs C σ ⟨o.1.val, h⟩
     else (2 * (σ ⟨o.1.val, h⟩).val + 1) * C.b + fjOffs C σ ⟨o.1.val, h⟩)
  else o.2.val * C.b

theorem fj_disj_sl (C : ThreePartition) (hv : C.Valid) (σ : Fin (3 * C.t) → Fin C.t)
    (hσ : C.IsSolution σ) (j j' : Fin (3 * C.t + 1)) (i : Fin ((reductionInstance C).μ j))
    (i' : Fin ((reductionInstance C).μ j')) (hj : j.val < 3 * C.t) (hj' : ¬ j'.val < 3 * C.t)
    (hm : (reductionInstance C).mach ⟨j, i⟩ = (reductionInstance C).mach ⟨j', i'⟩) :
    fjSt C σ ⟨j, i⟩ + fjLn C ⟨j, i⟩ ≤ fjSt C σ ⟨j', i'⟩ ∨
      fjSt C σ ⟨j', i'⟩ + fjLn C ⟨j', i'⟩ ≤ fjSt C σ ⟨j, i⟩ := by
  have m2 := fj_mu_small C j hj
  have m2' := fj_mu_long C j' hj'
  have hi := i.isLt
  have hi' := i'.isLt
  rw [fj_mach_small C j hj, fj_mach_long C j' hj'] at hm
  simp only [fjSt, fjLn, hj, hj', dite_true, dite_false]
  have ha := fj_offs_add_le C σ hσ ⟨j.val, hj⟩
  have hk := (σ ⟨j.val, hj⟩).isLt
  generalize (σ ⟨j.val, hj⟩).val = k at *
  generalize fjOffs C σ ⟨j.val, hj⟩ = off at *
  generalize C.a ⟨j.val, hj⟩ = a at *
  by_cases a0 : i.val = 0
  · simp only [a0, if_true] at hm ⊢
    have : i'.val % 2 = 1 := by
      by_cases e : i'.val % 2 = 0 <;> simp_all
    rcases (show 2 * k + 1 ≤ i'.val ∨ i'.val + 1 ≤ 2 * k by omega) with h | h
    · have := Nat.mul_le_mul_right C.b h
      left; nlinarith
    · have := Nat.mul_le_mul_right C.b h
      right; nlinarith
  · simp only [a0, if_false] at hm ⊢
    have : i'.val % 2 = 0 := by
      by_cases e : i'.val % 2 = 0 <;> simp_all
    rcases (show 2 * k + 2 ≤ i'.val ∨ i'.val ≤ 2 * k by omega) with h | h
    · have := Nat.mul_le_mul_right C.b h
      left; nlinarith
    · have := Nat.mul_le_mul_right C.b (show i'.val + 1 ≤ 2 * k + 1 by omega)
      right; nlinarith

theorem fj_disj_ll (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t)
    (j j' : Fin (3 * C.t + 1)) (i : Fin ((reductionInstance C).μ j))
    (i' : Fin ((reductionInstance C).μ j')) (hj : ¬ j.val < 3 * C.t) (hj' : ¬ j'.val < 3 * C.t)
    (hne : (⟨j, i⟩ : (reductionInstance C).Op) ≠ ⟨j', i'⟩)
    (hm : (reductionInstance C).mach ⟨j, i⟩ = (reductionInstance C).mach ⟨j', i'⟩) :
    fjSt C σ ⟨j, i⟩ + fjLn C ⟨j, i⟩ ≤ fjSt C σ ⟨j', i'⟩ ∨
      fjSt C σ ⟨j', i'⟩ + fjLn C ⟨j', i'⟩ ≤ fjSt C σ ⟨j, i⟩ := by
  have hjj : j = j' := by apply Fin.ext; have := j.isLt; have := j'.isLt; omega
  subst hjj
  have hii : i.val ≠ i'.val := by
    intro e; apply hne; have : i = i' := Fin.ext e
    subst this; rfl
  rw [fj_mach_long C j hj, fj_mach_long C j hj] at hm
  simp only [fjSt, fjLn, hj, dite_false]
  have : i.val % 2 = i'.val % 2 := by
    by_cases e : i.val % 2 = 0 <;> by_cases e' : i'.val % 2 = 0 <;> simp_all
  rcases lt_or_gt_of_ne hii with h | h
  · have := Nat.mul_le_mul_right C.b (show i.val + 1 ≤ i'.val by omega)
    left; nlinarith
  · have := Nat.mul_le_mul_right C.b (show i'.val + 1 ≤ i.val by omega)
    right; nlinarith

theorem fj_disj (C : ThreePartition) (hv : C.Valid) (σ : Fin (3 * C.t) → Fin C.t)
    (hσ : C.IsSolution σ) (o o' : (reductionInstance C).Op) (hne : o ≠ o')
    (hm : (reductionInstance C).mach o = (reductionInstance C).mach o') :
    fjSt C σ o + fjLn C o ≤ fjSt C σ o' ∨ fjSt C σ o' + fjLn C o' ≤ fjSt C σ o := by
  obtain ⟨j, i⟩ := o
  obtain ⟨j', i'⟩ := o'
  by_cases hj : j.val < 3 * C.t <;> by_cases hj' : j'.val < 3 * C.t
  · have m2 := fj_mu_small C j hj
    have m2' := fj_mu_small C j' hj'
    have hi := i.isLt
    have hi' := i'.isLt
    rw [fj_mach_small C j hj, fj_mach_small C j' hj'] at hm
    have hc : (i.val = 0 ↔ i'.val = 0) := by
      by_cases a : i.val = 0 <;> by_cases b : i'.val = 0 <;> simp_all
    have hjj : j ≠ j' := by
      intro e
      subst e
      apply hne
      have : i = i' := by apply Fin.ext; omega
      subst this; rfl
    simp only [fjSt, fjLn, hj, hj', dite_true]
    have ha := fj_offs_add_le C σ hσ ⟨j.val, hj⟩
    have ha' := fj_offs_add_le C σ hσ ⟨j'.val, hj'⟩
    rcases lt_trichotomy (σ ⟨j.val, hj⟩) (σ ⟨j'.val, hj'⟩) with hl | he | hg
    · have hk : (σ ⟨j.val, hj⟩).val + 1 ≤ (σ ⟨j'.val, hj'⟩).val := hl
      have := Nat.mul_le_mul_right C.b (show 2 * (σ ⟨j.val, hj⟩).val + 2 ≤ 2 * (σ ⟨j'.val, hj'⟩).val by omega)
      left
      by_cases a : i.val = 0 <;> by_cases b : i'.val = 0 <;> simp_all <;> nlinarith
    · have hjj' : j.val ≠ j'.val := fun e => hjj (Fin.ext e)
      rcases lt_or_gt_of_ne hjj' with hl | hg
      · have := fj_offs_mono C σ ⟨j.val, hj⟩ ⟨j'.val, hj'⟩ hl he
        left
        by_cases a : i.val = 0 <;> by_cases b : i'.val = 0 <;> simp_all <;> nlinarith
      · have := fj_offs_mono C σ ⟨j'.val, hj'⟩ ⟨j.val, hj⟩ hg he.symm
        right
        by_cases a : i.val = 0 <;> by_cases b : i'.val = 0 <;> simp_all <;> nlinarith
    · have hk : (σ ⟨j'.val, hj'⟩).val + 1 ≤ (σ ⟨j.val, hj⟩).val := hg
      have := Nat.mul_le_mul_right C.b (show 2 * (σ ⟨j'.val, hj'⟩).val + 2 ≤ 2 * (σ ⟨j.val, hj⟩).val by omega)
      right
      by_cases a : i.val = 0 <;> by_cases b : i'.val = 0 <;> simp_all <;> nlinarith
  · exact fj_disj_sl C hv σ hσ j j' i i' hj hj' hm
  · exact (fj_disj_sl C hv σ hσ j' j i' i hj' hj hm.symm).symm
  · exact fj_disj_ll C σ j j' i i' hj hj' hne hm

theorem fj_prec (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t)
    (hσ : C.IsSolution σ) (j : Fin (3 * C.t + 1)) (i i' : Fin ((reductionInstance C).μ j))
    (h : i.val + 1 = i'.val) :
    fjSt C σ ⟨j, i⟩ + fjLn C ⟨j, i⟩ ≤ fjSt C σ ⟨j, i'⟩ := by
  by_cases hj : j.val < 3 * C.t
  · have m2 := fj_mu_small C j hj
    have ha := fj_offs_add_le C σ hσ ⟨j.val, hj⟩
    have hi := i'.isLt
    have : i.val = 0 := by omega
    have h1 : i'.val ≠ 0 := by omega
    simp only [fjSt, fjLn, hj, dite_true, this, h1, if_true, if_false]
    nlinarith
  · simp only [fjSt, fjLn, hj, dite_false]
    nlinarith [h]

theorem fj_fin (C : ThreePartition) (σ : Fin (3 * C.t) → Fin C.t)
    (hσ : C.IsSolution σ) (o : (reductionInstance C).Op) :
    fjSt C σ o + fjLn C o ≤ 2 * C.t * C.b := by
  obtain ⟨j, i⟩ := o
  by_cases hj : j.val < 3 * C.t
  · have m2 := fj_mu_small C j hj
    have ha := fj_offs_add_le C σ hσ ⟨j.val, hj⟩
    have hi := i.isLt
    have hk := (σ ⟨j.val, hj⟩).isLt
    have := Nat.mul_le_mul_right C.b (show 2 * (σ ⟨j.val, hj⟩).val + 2 ≤ 2 * C.t by omega)
    simp only [fjSt, fjLn, hj, dite_true]
    by_cases a0 : i.val = 0 <;> simp only [a0, if_true, if_false] <;> nlinarith
  · have m2 := fj_mu_long C j hj
    have hi := i.isLt
    have := Nat.mul_le_mul_right C.b (show i.val + 1 ≤ 2 * C.t by omega)
    simp only [fjSt, fjLn, hj, dite_false]
    nlinarith

theorem fj_feasible (C : ThreePartition) (hv : C.Valid) (σ : Fin (3 * C.t) → Fin C.t)
    (hσ : C.IsSolution σ) :
    NonpreemptiveFinishesBy (reductionInstance C) (fun o => (fjSt C σ o : ℝ)) (threshold C) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro o _; positivity
  · intro j _ i i' h
    have := fj_prec C σ hσ j i i' h
    have e : (reductionInstance C).p j i = (fjLn C ⟨j, i⟩ : ℝ) := fj_proc C ⟨j, i⟩
    rw [e]
    exact_mod_cast this
  · intro o o' _ _ hne hm
    rw [fj_proc, fj_proc]
    rcases fj_disj C hv σ hσ o o' hne hm with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  · intro o
    rw [fj_proc]
    have := fj_fin C σ hσ o
    unfold threshold
    show (fjSt C σ o : ℝ) + _ ≤ _
    exact_mod_cast this

theorem fj_lemma_7a_core (C : ThreePartition) (hvalid : C.Valid) (hsol : C.HasSolution) :
    ∃ s : (reductionInstance C).Op → ℝ,
      NonpreemptiveFinishesBy (reductionInstance C) s (threshold C) := by
  obtain ⟨σ, hσ⟩ := hsol
  exact ⟨_, fj_feasible C hvalid σ hσ⟩


theorem fj_np_prec_aux (C : ThreePartition) (s : (reductionInstance C).Op → ℝ)
    (hs : (reductionInstance C).IsFeasibleSchedule Finset.univ s) (j : Fin (3 * C.t + 1)) :
    ∀ d : ℕ, ∀ i i' : Fin ((reductionInstance C).μ j), i.val + d + 1 = i'.val →
      s ⟨j, i⟩ + (reductionInstance C).proc ⟨j, i⟩ ≤ s ⟨j, i'⟩ := by
  intro d
  induction d with
  | zero =>
    intro i i' h
    exact hs.precedence j (Finset.mem_univ _) i i' (by omega)
  | succ d ih =>
    intro i i' h
    have hm : i.val + 1 < (reductionInstance C).μ j := by have := i'.isLt; omega
    let m : Fin ((reductionInstance C).μ j) := ⟨i.val + 1, hm⟩
    have h1 := hs.precedence j (Finset.mem_univ _) i m (by simp [m])
    have h2 := ih m i' (by simp [m]; omega)
    have h3 := (reductionInstance C).p_nonneg j m
    have h4 : (reductionInstance C).proc ⟨j, m⟩ = (reductionInstance C).p j m := rfl
    have h5 : (reductionInstance C).proc ⟨j, i⟩ = (reductionInstance C).p j i := rfl
    linarith

theorem fj_np_prec (C : ThreePartition) (s : (reductionInstance C).Op → ℝ)
    (hs : (reductionInstance C).IsFeasibleSchedule Finset.univ s)
    (o o' : (reductionInstance C).Op) (h1 : o.1 = o'.1) (h2 : o.2.val < o'.2.val) :
    s o + (reductionInstance C).proc o ≤ s o' := by
  obtain ⟨j, i⟩ := o
  obtain ⟨j', i'⟩ := o'
  simp only at h1 h2
  subst h1
  exact fj_np_prec_aux C s hs j (i'.val - i.val - 1) i i' (by omega)

/-- a nonpreemptive schedule yields a preemptive one with one piece per operation -/
noncomputable def fjPre (C : ThreePartition) (hv : C.Valid) (s : (reductionInstance C).Op → ℝ)
    (hs : NonpreemptiveFinishesBy (reductionInstance C) s (threshold C)) :
    PreemptiveSchedule (reductionInstance C) where
  pieceCount := Fintype.card (reductionInstance C).Op
  op := fun u => (Fintype.equivFin (reductionInstance C).Op).symm u
  start := fun u => s ((Fintype.equivFin (reductionInstance C).Op).symm u)
  finish := fun u => s ((Fintype.equivFin (reductionInstance C).Op).symm u)
    + (reductionInstance C).proc ((Fintype.equivFin (reductionInstance C).Op).symm u)
  piece_positive := by
    intro u
    refine ⟨hs.1.start_nonneg _ (Finset.mem_univ _), ?_⟩
    have : 0 < (reductionInstance C).proc ((Fintype.equivFin (reductionInstance C).Op).symm u) := by
      rw [fj_proc']
      unfold fjPrc
      split_ifs with h
      · have := (hv.2.2 ⟨_, h⟩).1
        have := hv.1
        have : 0 < C.a ⟨_, h⟩ := by omega
        exact_mod_cast this
      · exact_mod_cast hv.1
    linarith
  machine_disjoint := by
    intro u v huv hm
    have hne : (Fintype.equivFin (reductionInstance C).Op).symm u
        ≠ (Fintype.equivFin (reductionInstance C).Op).symm v := by
      intro h; exact huv ((Fintype.equivFin (reductionInstance C).Op).symm.injective h)
    exact hs.1.machine_disjoint _ _ (Finset.mem_univ _) (Finset.mem_univ _) hne hm
  work := by
    intro o
    have : Finset.univ.filter (fun u : Fin (Fintype.card (reductionInstance C).Op) =>
        (Fintype.equivFin (reductionInstance C).Op).symm u = o)
        = {Fintype.equivFin (reductionInstance C).Op o} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; rw [← h]; simp
      · intro h; rw [h]; simp
    rw [this, Finset.sum_singleton]
    simp
  precedence := by
    intro u v h1 h2
    exact fj_np_prec C s hs.1 _ _ h1 h2

theorem fj_pre_finishes (C : ThreePartition) (hv : C.Valid) (s : (reductionInstance C).Op → ℝ)
    (hs : NonpreemptiveFinishesBy (reductionInstance C) s (threshold C)) :
    (fjPre C hv s hs).FinishesBy (threshold C) := by
  intro u
  exact hs.2 _

theorem fj_lemma_7_preemptive_core (C : ThreePartition) (hvalid : C.Valid) :
    (∃ S : PreemptiveSchedule (reductionInstance C),
      S.FinishesBy (threshold C)) ↔ C.HasSolution := by
  constructor
  · rintro ⟨S, hS⟩
    by_contra hno
    obtain ⟨u, hu⟩ := fj_lemma_7b_core C hvalid hno S
    exact absurd (hS u) (not_le.mpr hu)
  · intro hsol
    obtain ⟨s, hs⟩ := fj_lemma_7a_core C hvalid hsol
    exact ⟨fjPre C hvalid s hs, fj_pre_finishes C hvalid s hs⟩

theorem fj_lemma_7_core (C : ThreePartition) (hvalid : C.Valid) :
    ((∃ S : PreemptiveSchedule (reductionInstance C),
      S.FinishesBy (threshold C)) ↔ C.HasSolution) ∧
    ((∃ s : (reductionInstance C).Op → ℝ,
      NonpreemptiveFinishesBy (reductionInstance C) s (threshold C)) ↔
        C.HasSolution) := by
  refine ⟨fj_lemma_7_preemptive_core C hvalid, ?_⟩
  constructor
  · rintro ⟨s, hs⟩
    exact (fj_lemma_7_preemptive_core C hvalid).1 ⟨fjPre C hvalid s hs, fj_pre_finishes C hvalid s hs⟩
  · exact fj_lemma_7a_core C hvalid

end FlowJobShop.ThreePartJob

open FlowJobShop.ThreePartJob
open ResourceScheduling.Chain

theorem solution (C : ThreePartition) (hvalid : C.Valid) :
    (∃ S : PreemptiveSchedule (reductionInstance C),
      S.FinishesBy (threshold C)) ↔ C.HasSolution := by
  exact fj_lemma_7_preemptive_core C hvalid
