-- Prove2me | solution 1 for FlowJobShop.ThreePartJob.lemma_7a
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:34:55.756854+00:00
-- url     : https://prove2.me/submissions/36e35faa-4aac-4695-9349-2732ccf1d6c2

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

end FlowJobShop.ThreePartJob

open FlowJobShop.ThreePartJob
open ResourceScheduling.Chain

theorem solution (C : ThreePartition) (hvalid : C.Valid) (hsol : C.HasSolution) :
    ∃ s : (reductionInstance C).Op → ℝ,
      NonpreemptiveFinishesBy (reductionInstance C) s (threshold C) := by
  exact fj_lemma_7a_core C hvalid hsol
