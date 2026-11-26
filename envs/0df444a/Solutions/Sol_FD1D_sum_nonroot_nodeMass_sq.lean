-- Prove2me | solution 1 for FD1D.sum_nonroot_nodeMass_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:03:20.674449+00:00
-- url     : https://prove2.me/submissions/d0affba5-bc8b-460d-9b1f-4e623201fdd2

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_weightedLevel_zero
import Theorems.Thm_FD1D_sum_nodeMass_sq
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.weightedLevel_zero

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution (L : ℕ) :
    nonrootMassSqSum L = 1 - 1 / (2 ^ L : ℝ) := by
  induction L with
  | zero =>
      simp [nonrootMassSqSum]
  | succ L ih =>
      rw [nonrootMassSqSum, Finset.sum_range_succ, sum_nodeMass_sq]
      rw [show (∑ d ∈ Finset.range L,
          ∑ v : DyadicNode (d + 1), (nodeMass (d + 1) v) ^ 2) =
          nonrootMassSqSum L by rfl, ih]
      simp only [pow_succ]
      field_simp
      ring
end FD1D
