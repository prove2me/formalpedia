-- Prove2me | solution 1 for GKP1998.mass_radius_relation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:19:14.948174+00:00
-- url     : https://prove2.me/submissions/1bf15543-a474-426b-a12e-6eb56830c1ed

import Mathlib
import Definitions.Def_GKP1998_Defs

set_option autoImplicit false

open Filter Topology Asymptotics

open GKP1998 in
theorem solution (n : ℕ) (N gYM α' m R : ℝ) (hN : 0 < N) (hg : 0 < gYM)
    (hα : 0 < α') (hm : 0 < m) (hR : 0 < R) (hmass : m ^ 2 = 4 * n / α')
    (hradius : R ^ 4 = 2 * N * gYM ^ 2 * α' ^ 2) :
    (m * R) ^ 2 = 4 * n * gYM * Real.sqrt (2 * N) := by
  have hs : 0 ≤ Real.sqrt (2 * N) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (2 * N) ^ 2 = 2 * N := Real.sq_sqrt (by positivity)
  have hR2 : R ^ 2 = gYM * α' * Real.sqrt (2 * N) := by
    have h1 : (R ^ 2) ^ 2 = (gYM * α' * Real.sqrt (2 * N)) ^ 2 := by
      rw [← pow_mul, hradius]
      have : (gYM * α' * Real.sqrt (2 * N)) ^ 2 = gYM ^ 2 * α' ^ 2 * Real.sqrt (2 * N) ^ 2 := by
        ring
      rw [this, hs2]
      ring
    exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).1 h1
  rw [mul_pow, hmass, hR2]
  field_simp
