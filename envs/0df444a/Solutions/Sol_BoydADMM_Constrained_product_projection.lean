-- Prove2me | solution 1 for BoydADMM.Constrained.product_projection
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:12:35.960107+00:00
-- url     : https://prove2.me/submissions/6dbbef03-88ca-4101-8892-45ac2e19c3fe

import Definitions.Def_BoydADMM_Constrained_Geometry

open BoydADMM.Constrained
open scoped BigOperators

theorem solution {N n : ℕ} (hN : 0 < N)
    (A : Fin N → Set (Vec n))
    (hAne : ∀ i, (A i).Nonempty) (hAclosed : ∀ i, IsClosed (A i))
    (hAconvex : ∀ i, Convex ℝ (A i))
    (v p : Blocks N n) :
    IsBlockProjection (productSet A) v p ↔
      ∀ i, RandomGradFree.Nonsmooth.IsMetricProjection (A i) (v i) (p i) := by
  classical
  constructor
  · rintro ⟨hp, hmin⟩ i
    refine ⟨hp i, ?_⟩
    intro w hw
    let q : Blocks N n := Function.update p i w
    have hq : q ∈ productSet A := by
      intro j
      by_cases hj : j = i
      · subst j
        simpa [q] using hw
      · simpa [q, hj] using hp j
    have hle := hmin q hq
    have hrest : (∑ j ∈ Finset.univ.erase i, ‖v j - q j‖ ^ 2) =
        ∑ j ∈ Finset.univ.erase i, ‖v j - p j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [q, (Finset.mem_erase.mp hj).1]
    have hpSum := Finset.sum_erase_add Finset.univ (fun j => ‖v j - p j‖ ^ 2)
      (Finset.mem_univ i)
    have hqSum := Finset.sum_erase_add Finset.univ (fun j => ‖v j - q j‖ ^ 2)
      (Finset.mem_univ i)
    simp only [blockSqDist] at hle
    rw [← hpSum, ← hqSum, hrest] at hle
    have hsq : ‖v i - p i‖ ^ 2 ≤ ‖v i - w‖ ^ 2 := by
      simpa [q] using (add_le_add_iff_left _).mp hle
    nlinarith [norm_nonneg (v i - p i), norm_nonneg (v i - w)]
  · intro hp
    refine ⟨fun i => (hp i).1, ?_⟩
    intro w hw
    apply Finset.sum_le_sum
    intro i _
    exact pow_le_pow_left₀ (norm_nonneg (v i - p i)) ((hp i).2 (w i) (hw i)) 2

#print axioms solution
