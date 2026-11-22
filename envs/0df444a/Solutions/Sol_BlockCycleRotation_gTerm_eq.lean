-- Prove2me | solution 1 for BlockCycleRotation.gTerm_eq
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T11:33:06.850112+00:00
-- url     : https://prove2.me/submissions/5b18ea30-bb22-4748-ae42-21b401cbf685

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem solution (p : ℕ × ℕ) : gTerm p = (zTerm p - eTerm p) / 2 := by
  unfold gTerm zTerm eTerm
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have ha : (0 : ℝ) < (p.1 : ℝ) := by
      have : 0 < p.1 := by omega
      exact_mod_cast this
    have ha' : (0 : ℝ) < (p.2 : ℝ) := by
      have : 0 < p.2 := by omega
      exact_mod_cast this
    have haa : (0 : ℝ) < (p.1 : ℝ) + (p.2 : ℝ) := by linarith
    field_simp
    ring
  · norm_num
