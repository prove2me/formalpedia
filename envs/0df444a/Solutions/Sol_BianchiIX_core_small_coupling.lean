-- Prove2me | solution 1 for BianchiIX.core_small_coupling
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:58:55.92777+00:00
-- url     : https://prove2.me/submissions/b31449b9-f087-43e9-ace7-42f85585c0d2

import Definitions.Def_BianchiIX_Algebra_Projective
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

noncomputable section
open BianchiIX


theorem solution {r m u v w : ℝ}
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hrm : r * m ≤ 1 / 1000)
    (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m) (hv : 1 ≤ v ∧ v ≤ r) :
    0 ≤ coupling u v w ∧ coupling u v w ≤ r * m + m ^ 2 ∧ coupling u v w ≤ 1 / 100 := by
  have hC0 : 0 ≤ coupling u v w := mul_nonneg hu.1 (by linarith [hm.2, hv.1])
  have hC : coupling u v w ≤ m * (r + m) := by
    unfold coupling
    apply mul_le_mul hu.2 (by linarith [hv.2]) (by linarith [hm.2, hv.1]) hm.1
  have hm2 : m ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := (sq_le_sq₀ hm.1 (by norm_num)).mpr hm.2
  exact ⟨hC0, by nlinarith, by nlinarith⟩
