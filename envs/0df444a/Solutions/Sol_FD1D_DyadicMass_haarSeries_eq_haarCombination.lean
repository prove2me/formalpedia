-- Prove2me | solution 1 for FD1D.DyadicMass.haarSeries_eq_haarCombination
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:03.658902+00:00
-- url     : https://prove2.me/submissions/47149f13-c81f-404d-a031-0503c95fedb9

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_DyadicMass_branch_succ_fiber
import Theorems.Thm_FD1D_DyadicMass_haarCombination_leftNode
import Theorems.Thm_FD1D_DyadicMass_haarCombination_rightNode
import Theorems.Thm_FD1D_DyadicMass_haarCombination_eq_zero_of_outside
import Theorems.Thm_FD1D_DyadicMass_branch_root_fiber
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


section
namespace FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace DyadicMass
end DyadicMass
namespace HaarTerm
end HaarTerm
private theorem dyadicTent_eq_unitTent_affine {a p z : ℝ}
    (hp : 0 < p) (hz0 : a ≤ z) (hz1 : z ≤ a + p) :
    dyadicTent a p z = DyadicMass.unitTent ((z - a) / p) := by
  by_cases hz : z ≤ a + p / 2
  · have hmem : z ∈ Icc a (a + p / 2) := ⟨hz0, hz⟩
    have hnot : z ∉ Ioc (a + p / 2) (a + p) := by
      intro h
      linarith [h.1]
    have hhalf : (z - a) / p ≤ 1 / 2 := by
      apply (div_le_iff₀ hp).2
      linarith
    rw [DyadicMass.unitTent, if_pos hhalf]
    simp [dyadicTent, hmem, hnot]
  · have hnot : z ∉ Icc a (a + p / 2) := by
      intro h
      exact hz h.2
    have hmem : z ∈ Ioc (a + p / 2) (a + p) :=
      ⟨lt_of_not_ge hz, hz1⟩
    have hhalf : ¬(z - a) / p ≤ 1 / 2 := by
      intro h
      have := (div_le_iff₀ hp).1 h
      linarith
    simp only [dyadicTent, Set.indicator_of_notMem hnot,
      Set.indicator_of_mem hmem, zero_add, DyadicMass.unitTent,
      if_neg hhalf]
    field_simp
    ring
namespace DyadicMass
end DyadicMass
namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
end FiniteLaw
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace DyadicMass
end DyadicMass
namespace MonotoneQuantilePolicy
end MonotoneQuantilePolicy
namespace FiniteLaw
end FiniteLaw
end
end FD1D
end

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution {L : ℕ} (q : DyadicMass L) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.haarSeries z =
      haarCombination haarNodeLeft haarNodeWidth q.nodeCoefficient z := by
  induction q generalizing z with
  | leaf =>
      simp [haarSeries, haarCombination]
  | @branch L l r ihl ihr =>
      unfold haarCombination
      rw [Fintype.sum_sigma, Fin.sum_univ_succ]
      simp_rw [branch_succ_fiber]
      rw [Finset.sum_add_distrib]
      rw [← Fintype.sum_sigma (fun v : CompleteHaarNode L =>
        l.nodeCoefficient v * dyadicTent (haarNodeLeft (leftNode v))
          (haarNodeWidth (leftNode v)) z)]
      rw [← Fintype.sum_sigma (fun v : CompleteHaarNode L =>
        r.nodeCoefficient v * dyadicTent (haarNodeLeft (rightNode v))
          (haarNodeWidth (rightNode v)) z)]
      rw [haarCombination_leftNode, haarCombination_rightNode]
      have htent : dyadicTent 0 1 z = unitTent z := by
        simpa using dyadicTent_eq_unitTent_affine
          (a := 0) (p := 1) (z := z) (by norm_num) hz0 (by simpa using hz1)
      rw [branch_root_fiber]
      rw [htent]
      simp only [haarSeries]
      by_cases hz : z ≤ 1 / 2
      · rw [if_pos hz, ihl (by linarith) (by linarith)]
        rw [haarCombination_eq_zero_of_outside r.nodeCoefficient
          (Or.inl (by linarith : 2 * z - 1 ≤ 0))]
        ring
      · rw [if_neg hz, ihr (by linarith) (by linarith)]
        rw [haarCombination_eq_zero_of_outside l.nodeCoefficient
          (Or.inr (by linarith : 1 ≤ 2 * z))]
        ring
end FD1D.DyadicMass
