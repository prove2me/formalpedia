-- Prove2me | solution 1 for FlowJobShop.ThreePartJob.forced_long_job
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:38:46.712495+00:00
-- url     : https://prove2.me/submissions/ddb7d114-5949-4a7f-98ef-64aa40940dee

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

end FlowJobShop.ThreePartJob

open FlowJobShop.ThreePartJob
open ResourceScheduling.Chain

theorem solution (C : ThreePartition) (hvalid : C.Valid)
    (S : PreemptiveSchedule (reductionInstance C))
    (hfinish : S.FinishesBy (threshold C)) :
    ∀ u : Fin S.pieceCount, (S.op u).1.val = 3 * C.t →
      ((S.op u).2.val : ℝ) * C.b ≤ S.start u ∧
        S.finish u ≤ (((S.op u).2.val + 1 : ℕ) : ℝ) * C.b := by
  exact fj_forced_core C hvalid S hfinish
