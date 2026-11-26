-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.orderedBias_lt_parentMass_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:04.437798+00:00
-- url     : https://prove2.me/submissions/669b40da-4c92-4567-8f23-9842ba85d3ad

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
import Theorems.Thm_FD1D_V5_LocalPolicy_orderedBias_le_uniform
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_V5_LocalPolicy_inventory_pos
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution
    {a p h : ℝ} {x y : ℕ}
    (hh : 0 < h) (hxy : y ≤ x) (hy : 0 < y) :
    orderedBias a p h x y < parentMass h x y := by
  have hN : 0 < inventory x y := inventory_pos (by omega)
  have hq : 0 < parentMass h x y := mul_pos hN hh
  by_cases heq : x = y
  · subst x
    simpa [orderedBias] using hq
  have hbU : orderedBias a p h x y ≤ uniformCandidate h x y :=
    orderedBias_le_uniform (a := a) (p := p) (h := h) hxy hy
  have hgap :
      ((x : ℝ) - y) / inventory x y < 1 := by
    have hy' : 0 < (y : ℝ) := by exact_mod_cast hy
    apply (div_lt_one hN).2
    unfold inventory
    linarith
  unfold uniformCandidate at hbU
  calc
    orderedBias a p h x y
        ≤ parentMass h x y * ((x : ℝ) - y) /
            inventory x y := hbU
    _ = parentMass h x y *
          (((x : ℝ) - y) / inventory x y) := by ring
    _ < parentMass h x y * 1 :=
      mul_lt_mul_of_pos_left hgap hq
    _ = parentMass h x y := mul_one _
end FD1D.V5.LocalPolicy
