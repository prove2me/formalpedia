-- Prove2me | solution 1 for DeterioratingJobs.Weighted.proposition2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:05:50.406366+00:00
-- url     : https://prove2.me/submissions/5766ec06-8e1d-4d2d-b86b-aa4010bb9396

import Mathlib
import Definitions.Def_DeterioratingJobs_Weighted_Model



namespace DeterioratingJobs.Weighted

open MeasureTheory

theorem eq2_core {Ω : Type*} {N : ℕ}
    (X : Fin N → Ω → ℝ) (α : Fin N → ℝ) (π : Equiv.Perm (Fin N))
    (k : ℕ) (hk : k ≤ N) (ω : Ω) :
    DeterioratingJobs.Makespan.completionTime X α π k ω =
      ∑ i : Fin N with i.val < k,
        X (π i) ω * ∏ r : Fin N with i < r ∧ r.val < k, (1 + α (π r)) := by
  induction k with
  | zero => simp [DeterioratingJobs.Makespan.completionTime]
  | succ k ih =>
    have hkN : k < N := hk
    have ih' := ih hkN.le
    have hstep : DeterioratingJobs.Makespan.completionTime X α π (k+1) ω =
        DeterioratingJobs.Makespan.completionTime X α π k ω +
          DeterioratingJobs.Makespan.actualProcessingTime X α (π ⟨k, hkN⟩)
            (DeterioratingJobs.Makespan.completionTime X α π k ω) ω := by
      simp [DeterioratingJobs.Makespan.completionTime, hkN]
    rw [hstep, ih']
    unfold DeterioratingJobs.Makespan.actualProcessingTime
    have hs : (Finset.univ.filter (fun i : Fin N => i.val < k+1)) =
        insert ⟨k, hkN⟩ (Finset.univ.filter (fun i : Fin N => i.val < k)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]; omega
    rw [hs, Finset.sum_insert (by simp)]
    have hp : ∀ i : Fin N, i.val < k →
        (Finset.univ.filter (fun r : Fin N => i < r ∧ r.val < k+1)) =
        insert ⟨k, hkN⟩ (Finset.univ.filter (fun r : Fin N => i < r ∧ r.val < k)) := by
      intro i hi
      ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, Fin.lt_def]; omega
    have hp0 : (Finset.univ.filter (fun r : Fin N => (⟨k, hkN⟩ : Fin N) < r ∧ r.val < k+1)) = ∅ := by
      ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, Fin.lt_def]; omega
    rw [hp0, Finset.prod_empty, mul_one]
    have : ∀ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k),
        X (π i) ω * ∏ r : Fin N with i < r ∧ r.val < k+1, (1 + α (π r)) =
        (X (π i) ω * ∏ r : Fin N with i < r ∧ r.val < k, (1 + α (π r))) * (1 + α (π ⟨k, hkN⟩)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [hp i hi, Finset.prod_insert (by simp)]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul]
    ring

theorem eq8_core {Ω : Type*} {N : ℕ}
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (ω : Ω) :
    totalCost X α c π ω =
      ∑ k : Fin N, c (π k) *
        ∑ i : Fin N with i ≤ k,
          X (π i) ω * ∏ r : Fin N with i < r ∧ r ≤ k, (1 + α (π r)) := by
  unfold totalCost
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eq2_core X α π (k.val+1) k.isLt ω]
  have h1 : (Finset.univ.filter (fun i : Fin N => i.val < k.val + 1)) =
      Finset.univ.filter (fun i : Fin N => i ≤ k) := by
    apply Finset.filter_congr; intro i _; rw [Fin.le_def]; omega
  have h2 : ∀ i : Fin N, (Finset.univ.filter (fun r : Fin N => i < r ∧ r.val < k.val + 1)) =
      Finset.univ.filter (fun r : Fin N => i < r ∧ r ≤ k) := by
    intro i
    apply Finset.filter_congr; intro r _; rw [Fin.le_def]; omega
  rw [h1]
  simp only [h2]


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


theorem ct_nonneg {Ω : Type*} {N : ℕ} (X : Fin N → Ω → ℝ) (α : Fin N → ℝ)
    (hX0 : ∀ i ω, 0 ≤ X i ω) (hα : ∀ i, 0 < α i)
    (σ : Equiv.Perm (Fin N)) (k : ℕ) (hk : k ≤ N) (ω : Ω) :
    0 ≤ DeterioratingJobs.Makespan.completionTime X α σ k ω := by
  rw [eq2_core X α σ k hk ω]
  refine Finset.sum_nonneg fun i _ => mul_nonneg (hX0 _ _) (Finset.prod_nonneg fun r _ => ?_)
  have := hα (σ r); linarith

theorem ct_int {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (X : Fin N → Ω → ℝ) (α : Fin N → ℝ) (hX : ∀ i, Integrable (X i) P)
    (σ : Equiv.Perm (Fin N)) (k : ℕ) (hk : k ≤ N) :
    Integrable (fun ω => DeterioratingJobs.Makespan.completionTime X α σ k ω) P := by
  have : (fun ω => DeterioratingJobs.Makespan.completionTime X α σ k ω) =
      fun ω => ∑ i : Fin N with i.val < k,
        X (σ i) ω * ∏ r : Fin N with i < r ∧ r.val < k, (1 + α (σ r)) :=
    funext fun ω => eq2_core X α σ k hk ω
  rw [this]
  exact integrable_finset_sum _ fun i _ => (hX _).mul_const _

theorem cost_int {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ) (hX : ∀ i, Integrable (X i) P)
    (σ : Equiv.Perm (Fin N)) :
    Integrable (fun ω => totalCost X α c σ ω) P := by
  unfold totalCost
  exact integrable_finset_sum _ fun k _ => (ct_int P X α hX σ (k.val+1) k.isLt).const_mul _

theorem ineq_core (EXa EXb αa αb ca cb : ℝ) (hEb : 0 ≤ EXb) (hEa : 0 ≤ EXa)
    (hαa : 0 < αa) (hαb : 0 < αb) (hca : 0 < ca) (hcb : 0 < cb)
    (h1 : EXb * αa < EXa * αb) (h2 : αb * (ca * (1 + αa)) < αa * (cb * (1 + αb))) :
    EXb * ca * (1 + αa) ≤ EXa * cb * (1 + αb) := by
  have h3 : (EXb * αa) * (αb * (ca * (1 + αa))) ≤ (EXa * αb) * (αa * (cb * (1 + αb))) :=
    mul_le_mul h1.le h2.le (by positivity) (by positivity)
  have h4 : (EXb * ca * (1 + αa)) * (αa * αb) ≤ (EXa * cb * (1 + αb)) * (αa * αb) := by
    nlinarith [h3]
  exact le_of_mul_le_mul_right h4 (mul_pos hαa hαb)

theorem step_core {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ)
    (hX : ∀ i, Integrable (X i) P)
    (hX0 : ∀ i ω, 0 ≤ X i ω)
    (hα : ∀ i, 0 < α i) (hc : ∀ i, 0 < c i)
    (hindex : StrictMono (fun i : Fin N => (∫ ω, X i ω ∂P) / α i))
    (hcost : StrictMono (fun i : Fin N => α i / (c i * (1 + α i))))
    (π : Equiv.Perm (Fin N)) (p : Fin N) (hp : p.val + 1 < N)
    (hdesc : π ⟨p.val + 1, hp⟩ < π p) :
    (∫ ω, totalCost X α c (π * Equiv.swap p ⟨p.val + 1, hp⟩) ω ∂P) ≤
      ∫ ω, totalCost X α c π ω ∂P := by
  set q : Fin N := ⟨p.val + 1, hp⟩ with hq
  set a := π p with ha
  set b := π q with hb
  have hm1 := hindex hdesc
  have hm2 := hcost hdesc
  simp only at hm1 hm2
  have hEa : 0 ≤ ∫ ω, X a ω ∂P := integral_nonneg fun ω => hX0 a ω
  have hEb : 0 ≤ ∫ ω, X b ω ∂P := integral_nonneg fun ω => hX0 b ω
  have hαa := hα a
  have hαb := hα b
  have hca := hc a
  have hcb := hc b
  rw [div_lt_div_iff₀ hαb hαa] at hm1
  rw [div_lt_div_iff₀ (mul_pos hcb (by linarith)) (mul_pos hca (by linarith))] at hm2
  have hm1' : (∫ ω, X b ω ∂P) * α a < (∫ ω, X a ω ∂P) * α b := hm1
  have hm2' : α b * (c a * (1 + α a)) < α a * (c b * (1 + α b)) := by linarith
  have hB := ineq_core _ _ _ _ _ _ hEb hEa hαa hαb hca hcb hm1' hm2'
  have hcoef : 0 ≤ c b * α a * (1 + α b) - c a * α b * (1 + α a) := by nlinarith
  have hdiffX : 0 ≤ (∫ ω, X a ω ∂P) * α b - (∫ ω, X b ω ∂P) * α a := by linarith
  have hid := fun ω => interchange_core X α c π p hp ω
  simp only at hid
  set s : Ω → ℝ := fun ω => DeterioratingJobs.Makespan.completionTime X α π p.val ω with hs
  set C : Fin N → ℝ := fun r => c (π r) *
      (∏ k : Fin N with p.val + 2 ≤ k.val ∧ k ≤ r, (1 + α (π k))) with hC
  have hsint : Integrable s P := ct_int P X α hX π p.val p.isLt.le
  have hsnn : ∀ ω, 0 ≤ s ω := fun ω => ct_nonneg X α hX0 hα π p.val p.isLt.le ω
  have hCnn : ∀ r, 0 ≤ C r := fun r =>
    mul_nonneg (hc _).le (Finset.prod_nonneg fun k _ => by have := hα (π k); linarith)
  have hRHS : ∀ ω, totalCost X α c π ω - totalCost X α c (π * Equiv.swap p q) ω =
      (s ω * (c b * α a * (1 + α b) - c a * α b * (1 + α a)) +
        (X a ω * (c b * (1 + α b)) - X b ω * (c a * (1 + α a)))) +
      ∑ r : Fin N with p.val + 2 ≤ r.val, C r * (X a ω * α b - X b ω * α a) := by
    intro ω
    rw [hid ω]
    simp only [hC, hs]
    ring
  have hf : Integrable (fun ω => s ω * (c b * α a * (1 + α b) - c a * α b * (1 + α a))) P :=
    hsint.mul_const _
  have hg : Integrable (fun ω => X a ω * (c b * (1 + α b)) - X b ω * (c a * (1 + α a))) P :=
    ((hX a).mul_const _).sub ((hX b).mul_const _)
  have hh : ∀ r : Fin N, Integrable (fun ω => C r * (X a ω * α b - X b ω * α a)) P := fun r =>
    (((hX a).mul_const _).sub ((hX b).mul_const _)).const_mul _
  have hh' : Integrable (fun ω => ∑ r : Fin N with p.val + 2 ≤ r.val,
      C r * (X a ω * α b - X b ω * α a)) P :=
    integrable_finset_sum _ fun r _ => hh r
  have hI1 : 0 ≤ ∫ ω, s ω * (c b * α a * (1 + α b) - c a * α b * (1 + α a)) ∂P :=
    integral_nonneg fun ω => mul_nonneg (hsnn ω) hcoef
  have hI2 : 0 ≤ ∫ ω, (X a ω * (c b * (1 + α b)) - X b ω * (c a * (1 + α a))) ∂P := by
    rw [integral_sub ((hX a).mul_const _) ((hX b).mul_const _), integral_mul_const, integral_mul_const]
    nlinarith [hB]
  have hI3 : 0 ≤ ∫ ω, ∑ r : Fin N with p.val + 2 ≤ r.val,
      C r * (X a ω * α b - X b ω * α a) ∂P := by
    rw [integral_finset_sum _ fun r _ => hh r]
    refine Finset.sum_nonneg fun r _ => ?_
    rw [integral_const_mul, integral_sub ((hX a).mul_const _) ((hX b).mul_const _),
      integral_mul_const, integral_mul_const]
    exact mul_nonneg (hCnn r) hdiffX
  have hsub := integral_sub (cost_int P X α c hX π) (cost_int P X α c hX (π * Equiv.swap p q))
  have hcongr : (∫ ω, (totalCost X α c π ω - totalCost X α c (π * Equiv.swap p q) ω) ∂P) =
      (∫ ω, s ω * (c b * α a * (1 + α b) - c a * α b * (1 + α a)) ∂P) +
      (∫ ω, (X a ω * (c b * (1 + α b)) - X b ω * (c a * (1 + α a))) ∂P) +
      ∫ ω, ∑ r : Fin N with p.val + 2 ≤ r.val, C r * (X a ω * α b - X b ω * α a) ∂P := by
    have e1 := integral_add (hf.add hg) hh'
    have e2 := integral_add hf hg
    simp only [Pi.add_apply] at e1 e2
    rw [integral_congr_ae (Filter.Eventually.of_forall hRHS), e1, e2]
  have : (∫ ω, totalCost X α c π ω ∂P) - (∫ ω, totalCost X α c (π * Equiv.swap p q) ω ∂P) ≥ 0 := by
    have h := hsub.symm.trans hcongr
    linarith
  linarith


def potT {N : ℕ} (σ : Equiv.Perm (Fin N)) : ℕ := ∑ k : Fin N, k.val * (σ k).val

theorem potT_le {N : ℕ} (σ : Equiv.Perm (Fin N)) : potT σ ≤ N * (N * N) := by
  unfold potT
  calc ∑ k : Fin N, k.val * (σ k).val ≤ ∑ _k : Fin N, N * N :=
        Finset.sum_le_sum fun k _ => Nat.mul_le_mul k.isLt.le (σ k).isLt.le
    _ = N * (N * N) := by simp

theorem potT_swap {N : ℕ} (σ : Equiv.Perm (Fin N)) (p : Fin N) (hp : p.val + 1 < N)
    (hdesc : σ ⟨p.val + 1, hp⟩ < σ p) :
    potT σ < potT (σ * Equiv.swap p ⟨p.val + 1, hp⟩) := by
  set q : Fin N := ⟨p.val + 1, hp⟩ with hq
  have hqv : q.val = p.val + 1 := rfl
  have hpq : p ≠ q := by intro h; have := congrArg Fin.val h; simp [hqv] at this
  have h1p : (σ * Equiv.swap p q) p = σ q := by simp [Equiv.swap_apply_left]
  have h1q : (σ * Equiv.swap p q) q = σ p := by simp [Equiv.swap_apply_right]
  have h1o : ∀ r : Fin N, r ≠ p → r ≠ q → (σ * Equiv.swap p q) r = σ r := by
    intro r h1 h2; simp [Equiv.swap_apply_of_ne_of_ne h1 h2]
  have key : ∀ k : Fin N,
      k.val * ((σ * Equiv.swap p q) k).val +
        ((if k = p then p.val * (σ p).val else 0) + (if k = q then q.val * (σ q).val else 0)) =
      k.val * (σ k).val +
        ((if k = p then p.val * (σ q).val else 0) + (if k = q then q.val * (σ p).val else 0)) := by
    intro k
    by_cases hkp : k = p
    · subst hkp; simp [h1p, hpq]; ring
    by_cases hkq : k = q
    · subst hkq; simp [h1q, hkp]; ring
    · simp [hkp, hkq, h1o k hkp hkq]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => key k)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq',
    Finset.sum_ite_eq'] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  have hlt : (σ q).val < (σ p).val := hdesc
  unfold potT
  nlinarith [hsum, hqv]

theorem prop2_core {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ)
    (hX : ∀ i, Integrable (X i) P)
    (hX0 : ∀ i ω, 0 ≤ X i ω)
    (hα : ∀ i, 0 < α i) (hc : ∀ i, 0 < c i)
    (hindex : StrictMono (fun i : Fin N => (∫ ω, X i ω ∂P) / α i))
    (hcost : StrictMono (fun i : Fin N => α i / (c i * (1 + α i)))) :
    ∀ σ : Equiv.Perm (Fin N),
      (∫ ω, totalCost X α c 1 ω ∂P) ≤
        ∫ ω, totalCost X α c σ ω ∂P := by
  have key : ∀ d : ℕ, ∀ σ : Equiv.Perm (Fin N), N * (N * N) - potT σ = d →
      (∫ ω, totalCost X α c 1 ω ∂P) ≤ ∫ ω, totalCost X α c σ ω ∂P := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro σ hd
      by_cases hex : ∃ (p : Fin N) (hp : p.val + 1 < N), σ ⟨p.val + 1, hp⟩ < σ p
      · obtain ⟨p, hp, hdesc⟩ := hex
        have h1 := potT_swap σ p hp hdesc
        have h2 := potT_le (σ * Equiv.swap p ⟨p.val + 1, hp⟩)
        have := ih (N * (N * N) - potT (σ * Equiv.swap p ⟨p.val + 1, hp⟩)) (by omega) _ rfl
        exact this.trans (step_core P X α c hX hX0 hα hc hindex hcost σ p hp hdesc)
      · have hmono : StrictMono σ := by
          cases N with
          | zero => intro i; exact i.elim0
          | succ n =>
            rw [Fin.strictMono_iff_lt_succ]
            intro i
            have hp : i.castSucc.val + 1 < n + 1 := by simp
            have h1 := not_exists.mp hex i.castSucc
            have h2 := not_exists.mp h1 hp
            have hq : (⟨i.castSucc.val + 1, hp⟩ : Fin (n+1)) = i.succ := Fin.ext (by simp)
            rw [hq] at h2
            have hne : σ i.castSucc ≠ σ i.succ := fun h => by
              have := σ.injective h
              exact Fin.castSucc_lt_succ.ne this
            exact lt_of_le_of_ne (not_lt.mp h2) hne
        have : σ = 1 := by
          have := (StrictMono.range_inj hmono (strictMono_id : StrictMono (id : Fin N → Fin N))).mp (by
            rw [Set.range_id]; exact Set.range_eq_univ.mpr σ.surjective |>.trans rfl)
          exact Equiv.ext fun i => by simpa using congrFun this i
        subst this
        exact le_rfl
  intro σ
  exact key _ σ rfl

end DeterioratingJobs.Weighted

open DeterioratingJobs.Weighted
open MeasureTheory DeterioratingJobs.Weighted

theorem solution {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ)
    (hX : ∀ i, Integrable (X i) P)
    (hX0 : ∀ i ω, 0 ≤ X i ω)
    (hα : ∀ i, 0 < α i) (hc : ∀ i, 0 < c i)
    (hindex : StrictMono (fun i : Fin N => (∫ ω, X i ω ∂P) / α i))
    (hcost : StrictMono (fun i : Fin N => α i / (c i * (1 + α i)))) :
    ∀ σ : Equiv.Perm (Fin N),
      (∫ ω, totalCost X α c 1 ω ∂P) ≤
        ∫ ω, totalCost X α c σ ω ∂P := by
  exact prop2_core P X α c hX hX0 hα hc hindex hcost
