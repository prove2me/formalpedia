-- Prove2me | solution 1 for BoydADMM.Constrained.average_step
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:13:29.498997+00:00
-- url     : https://prove2.me/submissions/cfd2562c-0a05-44fe-add2-90027ad627a0

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

theorem solution {N n : ℕ} (hN : 0 < N) (A : Fin N → Set (Vec n))
    (hAne : ∀ i, (A i).Nonempty) (hAclosed : ∀ i, IsClosed (A i))
    (hAconvex : ∀ i, Convex ℝ (A i))
    (ρ : ℝ) (hρ : 0 < ρ)
    (x : ℕ → Blocks N n) (z : ℕ → Vec n) (u : ℕ → Blocks N n)
    (hrun : IsParallelRun A x z u) :
    ∀ k, z (k + 1) = avg (x (k + 1)) + avg (u k) ∧ avg (u (k + 1)) = 0 := by
  exact average_step_local hN A x z u hrun

#print axioms solution
