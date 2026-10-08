-- Prove2me | solution 1 for DeterioratingJobs.Weighted.interchange_identity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:01:47.693555+00:00
-- url     : https://prove2.me/submissions/2b527ba1-bca6-4ef9-a20b-3ca9f60cf0cb

import Mathlib
import Definitions.Def_DeterioratingJobs_Weighted_Model



namespace DeterioratingJobs.Weighted

open MeasureTheory

theorem ct_succ {Ω : Type*} {N : ℕ} (X : Fin N → Ω → ℝ) (α : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) (m : ℕ) (hm : m < N) (ω : Ω) :
    DeterioratingJobs.Makespan.completionTime X α σ (m+1) ω =
      DeterioratingJobs.Makespan.completionTime X α σ m ω * (1 + α (σ ⟨m, hm⟩)) + X (σ ⟨m, hm⟩) ω := by
  simp only [DeterioratingJobs.Makespan.completionTime, hm, dite_true,
    DeterioratingJobs.Makespan.actualProcessingTime]
  ring

theorem interchange_core {Ω : Type*} {N : ℕ}
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (p : Fin N) (hp : p.val + 1 < N) (ω : Ω) :
    let q : Fin N := ⟨p.val + 1, hp⟩
    let a := π p
    let b := π q
    let π₁ := π * Equiv.swap p q
    totalCost X α c π ω - totalCost X α c π₁ ω =
      DeterioratingJobs.Makespan.completionTime X α π p.val ω *
        (c b * α a * (1 + α b) - c a * α b * (1 + α a)) +
      (X a ω * c b * (1 + α b) - X b ω * c a * (1 + α a)) +
      ∑ r : Fin N with p.val + 2 ≤ r.val,
        c (π r) *
          (∏ k : Fin N with p.val + 2 ≤ k.val ∧ k ≤ r, (1 + α (π k))) *
          (X a ω * α b - X b ω * α a) := by
  intro q a b π₁
  have hqv : q.val = p.val + 1 := rfl
  have hpq : p ≠ q := by intro h; have := congrArg Fin.val h; simp [hqv] at this
  have h1p : π₁ p = b := by simp [π₁, b, Equiv.swap_apply_left]
  have h1q : π₁ q = a := by simp [π₁, a, Equiv.swap_apply_right]
  have h1o : ∀ r : Fin N, r ≠ p → r ≠ q → π₁ r = π r := by
    intro r h1 h2; simp [π₁, Equiv.swap_apply_of_ne_of_ne h1 h2]
  -- agreement of early completion times
  have hagree : ∀ m : ℕ, m ≤ p.val →
      DeterioratingJobs.Makespan.completionTime X α π m ω =
      DeterioratingJobs.Makespan.completionTime X α π₁ m ω := by
    intro m
    induction m with
    | zero => intro _; simp [DeterioratingJobs.Makespan.completionTime]
    | succ m ih =>
      intro hm
      have hmN : m < N := by omega
      rw [ct_succ X α π m hmN, ct_succ X α π₁ m hmN, ih (by omega)]
      have hne1 : (⟨m, hmN⟩ : Fin N) ≠ p := by intro h; have := congrArg Fin.val h; simp at this; omega
      have hne2 : (⟨m, hmN⟩ : Fin N) ≠ q := by intro h; have := congrArg Fin.val h; simp [hqv] at this; omega
      rw [h1o _ hne1 hne2]
  set s := DeterioratingJobs.Makespan.completionTime X α π p.val ω with hs
  have hpN : p.val < N := p.isLt
  have e1 : DeterioratingJobs.Makespan.completionTime X α π (p.val+1) ω = s * (1 + α a) + X a ω := by
    rw [ct_succ X α π p.val hpN]
  have e1' : DeterioratingJobs.Makespan.completionTime X α π₁ (p.val+1) ω = s * (1 + α b) + X b ω := by
    rw [ct_succ X α π₁ p.val hpN, ← hagree p.val le_rfl, h1p]
  have e2 : DeterioratingJobs.Makespan.completionTime X α π (p.val+2) ω =
      (s * (1 + α a) + X a ω) * (1 + α b) + X b ω := by
    rw [show p.val + 2 = (p.val+1)+1 from rfl, ct_succ X α π (p.val+1) hp, e1]
  have e2' : DeterioratingJobs.Makespan.completionTime X α π₁ (p.val+2) ω =
      (s * (1 + α b) + X b ω) * (1 + α a) + X a ω := by
    rw [show p.val + 2 = (p.val+1)+1 from rfl, ct_succ X α π₁ (p.val+1) hp, e1', h1q]
  -- difference propagation
  have hD : ∀ m : ℕ, p.val + 2 ≤ m → m ≤ N →
      DeterioratingJobs.Makespan.completionTime X α π m ω -
        DeterioratingJobs.Makespan.completionTime X α π₁ m ω =
      (X a ω * α b - X b ω * α a) *
        ∏ k : Fin N with p.val + 2 ≤ k.val ∧ k.val < m, (1 + α (π k)) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _
      have : (Finset.univ.filter (fun k : Fin N => p.val + 2 ≤ k.val ∧ k.val < p.val + 2)) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun k _ => by omega)
      rw [this, Finset.prod_empty, mul_one, e2, e2']; ring
    | succ m hm ih =>
      intro hmN'
      have hmN : m < N := by omega
      rw [ct_succ X α π m hmN, ct_succ X α π₁ m hmN]
      have hne1 : (⟨m, hmN⟩ : Fin N) ≠ p := by intro h; have := congrArg Fin.val h; simp at this; omega
      have hne2 : (⟨m, hmN⟩ : Fin N) ≠ q := by intro h; have := congrArg Fin.val h; simp [hqv] at this; omega
      rw [h1o _ hne1 hne2]
      have hset : (Finset.univ.filter (fun k : Fin N => p.val + 2 ≤ k.val ∧ k.val < m + 1)) =
          insert ⟨m, hmN⟩ (Finset.univ.filter (fun k : Fin N => p.val + 2 ≤ k.val ∧ k.val < m)) := by
        refine Finset.ext fun k => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hset, Finset.prod_insert (by simp)]
      have := ih (by omega)
      have key : DeterioratingJobs.Makespan.completionTime X α π m ω * (1 + α (π ⟨m, hmN⟩)) -
          DeterioratingJobs.Makespan.completionTime X α π₁ m ω * (1 + α (π ⟨m, hmN⟩)) =
          (DeterioratingJobs.Makespan.completionTime X α π m ω -
            DeterioratingJobs.Makespan.completionTime X α π₁ m ω) * (1 + α (π ⟨m, hmN⟩)) := by ring
      calc _ = DeterioratingJobs.Makespan.completionTime X α π m ω * (1 + α (π ⟨m, hmN⟩)) -
          DeterioratingJobs.Makespan.completionTime X α π₁ m ω * (1 + α (π ⟨m, hmN⟩)) := by ring
        _ = _ := by rw [key, this]; ring
  -- termwise decomposition
  unfold totalCost
  rw [← Finset.sum_sub_distrib]
  let g : Fin N → ℝ := fun k =>
    c (π k) * DeterioratingJobs.Makespan.completionTime X α π (k.val + 1) ω -
    c (π₁ k) * DeterioratingJobs.Makespan.completionTime X α π₁ (k.val + 1) ω
  have hg : ∀ k : Fin N, g k =
      (if k = p then g p else 0) + (if k = q then g q else 0) +
      (if p.val + 2 ≤ k.val then
        c (π k) * (∏ j : Fin N with p.val + 2 ≤ j.val ∧ j ≤ k, (1 + α (π j))) *
          (X a ω * α b - X b ω * α a) else 0) := by
    intro k
    by_cases hkp : k = p
    · subst hkp
      have : ¬ (k.val + 2 ≤ k.val) := by omega
      have h2 : k ≠ q := hpq
      simp [this, h2]
    by_cases hkq : k = q
    · rw [hkq]
      have : ¬ (p.val + 2 ≤ q.val) := by rw [hqv]; omega
      simp [this, hkp, hkq, hpq.symm]
    by_cases hk2 : p.val + 2 ≤ k.val
    · have hlt : k.val < N := k.isLt
      have hkv : ¬ k = p := hkp
      simp only [hkp, hkq, hk2, if_false, if_true, zero_add]
      have hh := hD (k.val+1) (by omega) (by omega)
      have hset : (Finset.univ.filter (fun j : Fin N => p.val + 2 ≤ j.val ∧ j.val < k.val + 1)) =
          Finset.univ.filter (fun j : Fin N => p.val + 2 ≤ j.val ∧ j ≤ k) := by
        apply Finset.filter_congr; intro j _; rw [Fin.le_def]; omega
      rw [hset] at hh
      show c (π k) * _ - c (π₁ k) * _ = _
      rw [h1o k hkp hkq]
      linear_combination c (π k) * hh
    · have hkv : k.val < p.val := by
        have h1 : k.val ≠ p.val := fun h => hkp (Fin.ext h)
        have h2 : k.val ≠ p.val + 1 := fun h => hkq (Fin.ext (by rw [hqv]; exact h))
        omega
      simp only [hkp, hkq, hk2, if_false, add_zero]
      show c (π k) * _ - c (π₁ k) * _ = 0
      rw [h1o k hkp hkq, ← hagree (k.val+1) (by omega)]
      ring
  rw [Finset.sum_congr rfl (fun k _ => hg k), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ p, Finset.sum_ite_eq' Finset.univ q, ← Finset.sum_filter]
  simp only [Finset.mem_univ, if_true]
  show g p + g q + _ = _
  have gp : g p = c a * (s * (1 + α a) + X a ω) - c b * (s * (1 + α b) + X b ω) := by
    show c (π p) * _ - c (π₁ p) * _ = _
    rw [h1p, e1, e1']
  have gq : g q = c b * ((s * (1 + α a) + X a ω) * (1 + α b) + X b ω) -
      c a * ((s * (1 + α b) + X b ω) * (1 + α a) + X a ω) := by
    show c (π q) * _ - c (π₁ q) * _ = _
    rw [h1q, show q.val + 1 = p.val + 2 from rfl, e2, e2']
  rw [gp, gq]
  ring

end DeterioratingJobs.Weighted

open DeterioratingJobs.Weighted


theorem solution {Ω : Type*} {N : ℕ}
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (p : Fin N) (hp : p.val + 1 < N) (ω : Ω) :
    let q : Fin N := ⟨p.val + 1, hp⟩
    let a := π p
    let b := π q
    let π₁ := π * Equiv.swap p q
    totalCost X α c π ω - totalCost X α c π₁ ω =
      DeterioratingJobs.Makespan.completionTime X α π p.val ω *
        (c b * α a * (1 + α b) - c a * α b * (1 + α a)) +
      (X a ω * c b * (1 + α b) - X b ω * c a * (1 + α a)) +
      ∑ r : Fin N with p.val + 2 ≤ r.val,
        c (π r) *
          (∏ k : Fin N with p.val + 2 ≤ k.val ∧ k ≤ r, (1 + α (π k))) *
          (X a ω * α b - X b ω * α a) := by
  exact interchange_core X α c π p hp ω
