-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.polyMom_contract_v
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:26:26.689981+00:00
-- url     : https://prove2.me/submissions/2ba19212-e4ed-474d-b3b1-a2bb24be6eca

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.polyMom_contract_v
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_metric_mulVec_lower
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

variable {e T : ℝ} {S Tc : Matrix (Fin 4) (Fin 4) ℝ} {u v : Fin 4 → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) :
    (polyMom e T S Tc u v).mulVec (lower v) = (-e) • (((4 / 3) * T) • v + (2 : ℝ) • u) := by

  have hvv : (vecMulVec u v).mulVec (lower v) = -u := by
    ext a
    have hsum : ∑ c, v c * lower v c = -1 := by simpa [minkSq] using hv
    simp [vecMulVec_apply, Matrix.mulVec, dotProduct, mul_assoc, ← Finset.mul_sum, hsum]
  have hml : metric.mulVec (lower v) = v := metric_mulVec_lower v
  rw [polyMom]
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, hS.right, hTc.right, hvv, hml]
  module
