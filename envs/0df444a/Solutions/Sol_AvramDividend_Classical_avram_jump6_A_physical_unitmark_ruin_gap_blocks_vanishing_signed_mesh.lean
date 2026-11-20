-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_physical_unitmark_ruin_gap_blocks_vanishing_signed_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:14:07.0752+00:00
-- url     : https://prove2.me/submissions/811f5b21-460b-429c-b58a-f02a01d58aec

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_unit_fullmark_ruin_gap_scalar_obstruction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Filter AvramDividend.Classical
noncomputable section
theorem solution
    (y b t : ℝ)
    (hy0 : 0 ≤ y) (hycap : y ≤ 1 / 5)
    (hb : b ≤ 1 / 100) (ht : t ≤ 1 / 10)
    (B E : ℕ → ℝ)
    (hB : ∀ m, B m ≤ 0)
    (hE : Tendsto E atTop (nhds (0 : ℝ)))
    (hLedger : ∀ m,
      0 ≤ (1 + y + y ^ 2) + b - 2 + 2 * t + B m + E m) :
    False := by
  obtain ⟨_, hgap⟩ :=
    avram_jump6_A_unit_fullmark_ruin_gap_scalar_obstruction
      y b t hy0 hycap hb ht
  have hEventually : ∀ᶠ m : ℕ in atTop, E m < (1 / 2 : ℝ) :=
    hE.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨m, hm⟩ := hEventually.exists
  have hBad := hLedger m
  have hDrift := hB m
  linarith
