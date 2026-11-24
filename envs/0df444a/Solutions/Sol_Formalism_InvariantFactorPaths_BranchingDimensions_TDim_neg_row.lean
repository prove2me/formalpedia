-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TDim.neg_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:11.815701+00:00
-- url     : https://prove2.me/submissions/99423aec-e724-4b0e-8593-67223c037fe9

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_sum_hh_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_le_sum_hh
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_pos_idx
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_neg_idx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Formalism.InvariantFactorPaths.BranchingDimensions.TDim
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TDim
theorem _root_.solution {r K Ns n : ℕ} {la : ℕ → ℤ} {L : ℝ} (h2 : 2 * Ns ≤ K) (hK : K ≤ n) (hn : n ≤ r + K)
    (hd : Dom n la) (hP : ((range n).filter fun m => 0 < la m).card ≤ Ns)
    (hM : ((range n).filter fun m => la m < 0).card ≤ Ns) (hL0 : 0 ≤ L)
    {j : ℕ} (hj : j < n) (hp : la j < 0) (hL : Real.log (1 + ((-la j : ℤ) : ℝ)) ≤ L) :
    fT (K - 2 * Ns) ((-la j : ℤ) : ℝ) - (Ns : ℝ) * L ≤
        ∑ i ∈ range j, (if la i = 0 then hh ((-la j : ℤ) : ℝ) (j - i) else 0) ∧
      ∑ i ∈ range j, (if la i = 0 then hh ((-la j : ℤ) : ℝ) (j - i) else 0) ≤
        fT (K - 2 * Ns) ((-la j : ℤ) : ℝ) + ((r : ℝ) + 2 * Ns) * L := by
  have h0 : (0 : ℤ) ≤ -la j := by omega
  have hz : (0 : ℝ) ≤ ((-la j : ℤ) : ℝ) := by exact_mod_cast h0
  have hjN : n ≤ j + Ns := neg_idx hd hM hj hp
  have hS : ∑ i ∈ range j, (if la i = 0 then Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh ((-la j : ℤ) : ℝ) (j - i) else 0) =
      ∑ d ∈ ((range j).filter (fun i => la i = 0)).image (fun i => j - i),
        Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh ((-la j : ℤ) : ℝ) d := by
    rw [Finset.sum_image, Finset.sum_filter]
    intro x hx y hy hxy
    have hxy' : j - x = j - y := hxy
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq,
      Finset.mem_coe] at hx hy
    omega
  rw [hS]
  generalize hDdef : ((range j).filter (fun i => la i = 0)).image (fun i => j - i) = D
  have hD : ∀ d ∈ D, 1 ≤ d := by
    intro x hx
    rw [← hDdef, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_filter, Finset.mem_range] at hi
    omega
  have hc1 : (D \ Icc 1 (K - 2 * Ns)).card ≤ r + 2 * Ns := by
    have hsub : D \ Icc 1 (K - 2 * Ns) ⊆ Ico (K - 2 * Ns + 1) n := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [← hDdef, Finset.mem_image] at hx1
      obtain ⟨i, hi, rfl⟩ := hx1
      rw [Finset.mem_filter, Finset.mem_range] at hi
      have hgt : K - 2 * Ns < j - i := by
        by_contra hh
        exact hx2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [Finset.mem_Ico]
      omega
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    omega
  have hc2 : (Icc 1 (K - 2 * Ns) \ D).card ≤ Ns := by
    have hsub : Icc 1 (K - 2 * Ns) \ D ⊆ Ico 1 Ns := by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_Icc] at hx
      obtain ⟨⟨hx1, hx2⟩, hxD⟩ := hx
      rw [Finset.mem_Ico]
      refine ⟨hx1, ?_⟩
      by_contra hlt
      apply hxD
      have hxj : x ≤ j := by omega
      have hin : j - x < n := by omega
      have hz0 : la (j - x) = 0 := by
        rcases lt_trichotomy (la (j - x)) 0 with h | h | h
        · have := neg_idx hd hM hin h
          omega
        · exact h
        · have := pos_idx hd hP hin h
          omega
      rw [← hDdef, Finset.mem_image]
      exact ⟨j - x, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hz0⟩, by omega⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    omega
  have hup := sum_hh_le hz hL D hD (K - 2 * Ns)
  have hlo := le_sum_hh hz hL D hD (K - 2 * Ns)
  have e1 : ((D \ Icc 1 (K - 2 * Ns)).card : ℝ) * L ≤ ((r : ℝ) + 2 * Ns) * L := by
    apply mul_le_mul_of_nonneg_right _ hL0
    exact_mod_cast hc1
  have e2 : ((Icc 1 (K - 2 * Ns) \ D).card : ℝ) * L ≤ (Ns : ℝ) * L := by
    apply mul_le_mul_of_nonneg_right _ hL0
    exact_mod_cast hc2
  constructor <;> linarith
end Formalism.InvariantFactorPaths.BranchingDimensions.TDim
