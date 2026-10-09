-- Prove2me | solution 1 for BookProof.ChapterCoherentThermalFidelity.dtOverlap_coherentParameter
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:37:54.382849+00:00
-- url     : https://prove2.me/submissions/db071937-1323-4dcb-9fd7-a046749d1478
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterCoherentThermalFidelity.lean — solution of BookProof.ChapterCoherentThermalFidelity.dtOverlap_coherentParameter
import Mathlib
import Definitions.Def_ChapterCoherentThermalFidelity
import Theorems.Thm_BookProof_ChapterDisplacedThermalOverlap_dtOverlap_eq
open BookProof.ChapterCoherentThermalFidelity



noncomputable section


open BookProof.ChapterCoherentOccupation BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentFidelity BookProof.ChapterDisplacedThermalOverlap
open Real

variable {nbar lam : ℝ}

variable {nbar lam : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (nb : NNReal) (a b : ℝ) :
    dtOverlap nb (Real.sqrt 2 * a) (Real.sqrt 2 * b)
      = Real.exp (-((a - b) ^ 2 / (((nb : ℝ) + 1 / 2) + ((nb : ℝ) + 1 / 2))))
        / Real.sqrt (4 * π * ((nb : ℝ) + 1 / 2)) := by

  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hτ : (0 : ℝ) < (nb : ℝ) + 1 / 2 := by positivity
  rw [dtOverlap_eq]
  congr 2
  have hsq : (Real.sqrt 2 * a - Real.sqrt 2 * b) ^ 2 = 2 * (a - b) ^ 2 := by
    rw [show Real.sqrt 2 * a - Real.sqrt 2 * b = Real.sqrt 2 * (a - b) by ring, mul_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [hsq]
  field_simp
  ring
