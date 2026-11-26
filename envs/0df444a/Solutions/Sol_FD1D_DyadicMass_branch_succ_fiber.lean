-- Prove2me | solution 1 for FD1D.DyadicMass.branch_succ_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:51.202451+00:00
-- url     : https://prove2.me/submissions/f4d4f5fa-5b87-4d96-a53e-f1cd9ff519aa

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_DyadicMass_succNode_castAdd_eq_leftNode
import Theorems.Thm_FD1D_DyadicMass_succNode_natAdd_eq_rightNode
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution {L : ℕ} (l r : DyadicMass L) (d : Fin L)
    (z : ℝ) :
    (∑ y : Fin (2 ^ d.succ.val),
      (branch l r).nodeCoefficient ⟨d.succ, y⟩ *
        dyadicTent (haarNodeLeft ⟨d.succ, y⟩)
          (haarNodeWidth ⟨d.succ, y⟩) z) =
      (∑ y : Fin (2 ^ d.val),
        l.nodeCoefficient ⟨d, y⟩ *
          dyadicTent (haarNodeLeft (leftNode ⟨d, y⟩))
            (haarNodeWidth (leftNode ⟨d, y⟩)) z) +
      ∑ y : Fin (2 ^ d.val),
        r.nodeCoefficient ⟨d, y⟩ *
          dyadicTent (haarNodeLeft (rightNode ⟨d, y⟩))
            (haarNodeWidth (rightNode ⟨d, y⟩)) z := by
  let e := childFinEquiv d.val
  change (∑ y : Fin (2 ^ (d.val + 1)),
    (branch l r).nodeCoefficient ⟨d.succ, y⟩ *
      dyadicTent (haarNodeLeft ⟨d.succ, y⟩)
        (haarNodeWidth ⟨d.succ, y⟩) z) = _
  rw [← e.sum_comp]
  rw [Fin.sum_univ_add]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro y _
    rw [succNode_castAdd_eq_leftNode]
    simp
  · apply Finset.sum_congr rfl
    intro y _
    rw [succNode_natAdd_eq_rightNode]
    simp
end FD1D.DyadicMass
