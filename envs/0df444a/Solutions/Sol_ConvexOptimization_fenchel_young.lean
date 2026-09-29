-- Prove2me | solution 1 for ConvexOptimization.fenchel_young
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T03:14:40.388818+00:00
-- url     : https://prove2.me/submissions/68c583d7-e0bb-4caf-ae59-ff108f54335c

import Mathlib
import Definitions.Def_fenchelConjugate

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

open ConvexOptimization in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ((⟪x, y⟫ : ℝ) : EReal) ≤ (f x : EReal) + fenchelConjugate f y := by
  have h : ((⟪x, y⟫ - f x : ℝ) : EReal) ≤ fenchelConjugate f y :=
    le_iSup (fun z : EuclideanSpace ℝ (Fin n) => ((⟪z, y⟫ - f z : ℝ) : EReal)) x
  have hsplit : ((⟪x, y⟫ : ℝ) : EReal) = (f x : EReal) + ((⟪x, y⟫ - f x : ℝ) : EReal) := by
    rw [← EReal.coe_add]
    norm_num
  rw [hsplit]
  gcongr
