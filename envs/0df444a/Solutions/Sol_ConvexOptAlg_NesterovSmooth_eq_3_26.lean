-- Prove2me | solution 1 for ConvexOptAlg.NesterovSmooth.eq_3_26
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:51:14.216908+00:00
-- url     : https://prove2.me/submissions/f57fabc8-b0b2-4338-8f28-b5b789cfd4a2

import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs
open scoped InnerProductSpace

open ConvexOptAlg.NesterovSmooth in
theorem solution {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovRun g β x y) (s : ℕ) (hs : 1 ≤ s) :
    lam (s + 1) • x (s + 1) - (lam (s + 1) - 1) • y (s + 1) =
      lam s • y (s + 1) - (lam s - 1) • y s := by
  obtain ⟨_, h⟩ := hrun
  rw [(h s hs).2]
  have hpos : 0 < lam (s + 1) := by
    simp only [lam]
    positivity
  have h2 : lam (s + 1) * gam s = 1 - lam s := by
    unfold gam
    field_simp
  have h1 : lam (s + 1) * (1 - gam s) = lam (s + 1) - 1 + lam s := by
    rw [mul_sub, h2]; ring
  rw [smul_add, smul_smul, smul_smul, h1, h2]
  module
