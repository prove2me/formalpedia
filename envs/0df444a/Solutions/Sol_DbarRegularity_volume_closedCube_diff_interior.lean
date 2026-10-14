-- Prove2me | solution 1 for DbarRegularity.volume_closedCube_diff_interior
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T15:32:40.241714+00:00
-- url     : https://prove2.me/submissions/9401e124-d450-41df-a82b-5349b9097d65

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Theorems.Thm_DbarRegularity_isClosed_closedCube
import Mathlib.Analysis.Convex.Measure



namespace DbarRegularity

open MeasureTheory Set

/-- The boundary `Q \ interior Q` of a closed cube in `ℝ^d` is a Lebesgue null set. -/
theorem volume_closedCube_diff_interior {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    volume (closedCube a s \ interior (closedCube a s)) = 0 := by
  have hconv : Convex ℝ (closedCube a s) := by
    intro x hx y hy t u ht hu htu i
    obtain ⟨hx1, hx2⟩ := hx i
    obtain ⟨hy1, hy2⟩ := hy i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have e : a i = t * a i + u * a i := by rw [← add_mul, htu, one_mul]
    constructor
    · nlinarith [mul_nonneg ht (sub_nonneg.2 hx1), mul_nonneg hu (sub_nonneg.2 hy1)]
    · nlinarith [mul_nonneg ht (sub_nonneg.2 hx2), mul_nonneg hu (sub_nonneg.2 hy2)]
  have h := hconv.addHaar_frontier (volume : Measure (EuclideanSpace ℝ (Fin d)))
  rwa [frontier, (isClosed_closedCube a s).closure_eq] at h

end DbarRegularity

open DbarRegularity

open MeasureTheory Set

theorem solution {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    volume (closedCube a s \ interior (closedCube a s)) = 0 :=
  volume_closedCube_diff_interior a s
