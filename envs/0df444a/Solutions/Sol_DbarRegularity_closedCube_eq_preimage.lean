-- Prove2me | solution 1 for DbarRegularity.closedCube_eq_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:50:39.476988+00:00
-- url     : https://prove2.me/submissions/c8baa431-37e2-4209-b65f-94f074ed7650

import Definitions.Def_DbarRegularity_Setting



namespace DbarRegularity

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal

theorem closedCube_eq_preimage {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    closedCube a s = (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) ⁻¹'
      Icc (fun i => a i) (fun i => a i + s) := by
  ext x
  simp [closedCube, Pi.le_def, forall_and]

end DbarRegularity

open DbarRegularity

open Set

theorem solution {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    closedCube a s = (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) ⁻¹'
      Icc (fun i => a i) (fun i => a i + s) :=
  closedCube_eq_preimage a s
