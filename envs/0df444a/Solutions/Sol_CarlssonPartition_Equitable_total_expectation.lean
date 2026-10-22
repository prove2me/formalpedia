-- Prove2me | solution 1 for CarlssonPartition.Equitable.total_expectation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:35:10.753533+00:00
-- url     : https://prove2.me/submissions/6fe30a3a-4675-426a-85bd-16c137063f24

import Mathlib
import Definitions.Def_CarlssonPartition_Equitable_Setting

set_option autoImplicit false
open Filter Topology MeasureTheory CarlssonPartition.Equitable

theorem solution (I : Instance) (hI : I.Standing)
    (Rs : Fin I.m → Set Plane) (hP : I.IsPartition Rs)
    (Tstar : ℝ → ℝ) (T : Fin I.m → ℝ → ℝ)
    (hT : ∀ i, Tendsto (fun lam => T i lam / Tstar lam) (I.heavy I.m I.R I.f) (𝓝 1)) :
    Tendsto (fun lam => (∑ i, I.pr (Rs i) * T i lam) / Tstar lam) (I.heavy I.m I.R I.f) (𝓝 1) := by
  obtain ⟨hnull, hdisj, hunion⟩ := hP
  have hint : IntegrableOn I.f I.R := by
    by_contra h
    have := hI.2.2.2.2.2.1
    rw [integral_undef h] at this
    exact zero_ne_one this
  have hsum : ∑ i, I.pr (Rs i) = 1 := by
    have h1 : ∫ x in ⋃ i, Rs i, I.f x = ∑' i, ∫ x in Rs i, I.f x :=
      integral_iUnion_ae hnull hdisj (by rwa [hunion])
    rw [hunion, tsum_fintype] at h1
    rw [← hI.2.2.2.2.2.1, h1]
    rfl
  have h2 : Tendsto (fun lam => ∑ i, I.pr (Rs i) * (T i lam / Tstar lam)) (I.heavy I.m I.R I.f)
      (𝓝 (∑ i, I.pr (Rs i) * 1)) :=
    tendsto_finset_sum _ fun i _ => (hT i).const_mul _
  simp only [mul_one, hsum] at h2
  refine h2.congr fun lam => ?_
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring
