-- Prove2me | solution 1 for BookProof.ChapterBaryonAsymmetry.radiation_satisfies_continuity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:16:29.994001+00:00
-- url     : https://prove2.me/submissions/0f0e7dee-4ab0-4fed-ae39-ed8f26271825

-- Generated from ChapterBaryonAsymmetry.lean — solution of BookProof.ChapterBaryonAsymmetry.radiation_satisfies_continuity
import Mathlib
import Definitions.Def_ChapterBaryonAsymmetry
open BookProof.ChapterBaryonAsymmetry













open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (ρr0 a : ℝ) (ha : 0 < a) :
    a * deriv (fun x => radDensity ρr0 x) a + 3 * (1 + 1/3) * radDensity ρr0 a = 0 := by

  have h : HasDerivAt (fun x : ℝ => radDensity ρr0 x)
      (ρr0 * (-(4 * a ^ 3) / (a ^ 4) ^ 2)) a := by
    have hp : HasDerivAt (fun x : ℝ => x ^ 4) (4 * a ^ 3) a := by simpa using hasDerivAt_pow 4 a
    have hinv : HasDerivAt (fun x : ℝ => (x ^ 4)⁻¹) (-(4 * a ^ 3) / (a ^ 4) ^ 2) a :=
      hp.inv (by positivity)
    simpa [radDensity, div_eq_mul_inv] using hinv.const_mul ρr0
  rw [h.deriv]
  simp only [radDensity]
  field_simp
  ring
