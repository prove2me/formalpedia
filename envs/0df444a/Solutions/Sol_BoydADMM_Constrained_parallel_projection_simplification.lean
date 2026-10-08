-- Prove2me | solution 1 for BoydADMM.Constrained.parallel_projection_simplification
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:14:03.240736+00:00
-- url     : https://prove2.me/submissions/245761b0-3b9f-4957-a30f-688887c21442

import Definitions.Def_BoydADMM_Constrained_Run

open BoydADMM.Constrained

private lemma avg_add_local {N n : ℕ} (v w : Blocks N n) :
    avg (fun i => v i + w i) = avg v + avg w := by
  simp [avg, Finset.sum_add_distrib, smul_add]

private lemma avg_sub_local {N n : ℕ} (v w : Blocks N n) :
    avg (fun i => v i - w i) = avg v - avg w := by
  simp [avg, Finset.sum_sub_distrib, smul_sub]

private lemma avg_const_local {N n : ℕ} (hN : 0 < N) (a : Vec n) :
    avg (fun _ : Fin N => a) = a := by
  simp only [avg, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [Nat.ne_of_gt hN]

private lemma average_step_local {N n : ℕ} (hN : 0 < N) (A : Fin N → Set (Vec n))
    (x : ℕ → Blocks N n) (z : ℕ → Vec n) (u : ℕ → Blocks N n)
    (hrun : IsParallelRun A x z u) :
    ∀ k, z (k + 1) = avg (x (k + 1)) + avg (u k) ∧ avg (u (k + 1)) = 0 := by
  intro k
  have hz : z (k + 1) = avg (x (k + 1)) + avg (u k) := by
    rw [hrun.z_average k, avg_add_local]
  refine ⟨hz, ?_⟩
  calc
    avg (u (k + 1)) = avg (fun i => u k i + x (k + 1) i - z (k + 1)) :=
      congrArg avg (funext (hrun.u_update k))
    _ = avg (u k) + avg (x (k + 1)) - z (k + 1) := by
      rw [avg_sub_local, avg_add_local, avg_const_local hN]
    _ = 0 := by rw [hz]; abel

theorem solution {N n : ℕ} (hN : 0 < N)
    (A : Fin N → Set (Vec n))
    (hAne : ∀ i, (A i).Nonempty) (hAclosed : ∀ i, IsClosed (A i))
    (hAconvex : ∀ i, Convex ℝ (A i))
    (ρ : ℝ) (hρ : 0 < ρ)
    (x : ℕ → Blocks N n) (z : ℕ → Vec n) (u : ℕ → Blocks N n)
    (hrun : IsParallelRun A x z u) :
    (∀ k, avg (u (k + 1)) = 0) ∧
    (∀ k, 1 ≤ k → z (k + 1) = avg (x (k + 1))) ∧
    (∀ k, 2 ≤ k → ∀ i,
      RandomGradFree.Nonsmooth.IsMetricProjection (A i)
        (avg (x k) - u k i) (x (k + 1) i) ∧
      u (k + 1) i = u k i + (x (k + 1) i - avg (x (k + 1)))) ∧
    (avg (u 0) = 0 → ∀ k, 1 ≤ k → ∀ i,
      RandomGradFree.Nonsmooth.IsMetricProjection (A i)
        (avg (x k) - u k i) (x (k + 1) i) ∧
      u (k + 1) i = u k i + (x (k + 1) i - avg (x (k + 1)))) := by
  have havg := average_step_local hN A x z u hrun
  have hzero : ∀ k, avg (u (k + 1)) = 0 := fun k => (havg k).2
  have hpositive : ∀ k, 1 ≤ k → avg (u k) = 0 := by
    intro k hk
    cases k with
    | zero => omega
    | succ k => exact hzero k
  have hz : ∀ k, 1 ≤ k → z (k + 1) = avg (x (k + 1)) := by
    intro k hk
    rw [(havg k).1, hpositive k hk, add_zero]
  have hcurrent : ∀ k, 2 ≤ k → z k = avg (x k) := by
    intro k hk
    cases k with
    | zero => omega
    | succ k => exact hz k (by omega)
  refine ⟨hzero, hz, ?_, ?_⟩
  · intro k hk i
    constructor
    · simpa only [hcurrent k hk] using hrun.x_project k i
    · rw [hrun.u_update k i, hz k (by omega)]
      abel
  · intro hu0 k hk i
    have hall : ∀ j, avg (u j) = 0 := by
      intro j
      cases j with
      | zero => exact hu0
      | succ j => exact hzero j
    have hzall : ∀ j, z (j + 1) = avg (x (j + 1)) := by
      intro j
      rw [(havg j).1, hall j, add_zero]
    have hzcurrent : z k = avg (x k) := by
      cases k with
      | zero => omega
      | succ j => exact hzall j
    constructor
    · simpa only [hzcurrent] using hrun.x_project k i
    · rw [hrun.u_update k i, hzall k]
      abel

#print axioms solution