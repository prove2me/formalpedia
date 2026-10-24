-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.norm_le_four_pow_mul_norm_symmetrize_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:04:13.728461+00:00
-- url     : https://prove2.me/submissions/5c394883-f502-4c21-9814-3769e7e79e5f

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_card_slots_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_norm_le_four_pow_mul_norm_blockAverage_408915f

noncomputable section
open Finset
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
/-- **BKL Lemma 2.2.** Let `d ≥ 0` and let `A` be a tensor with `k ≥ 3d` indices over `Fin n`,
invariant under permutations of its first `d` indices and under permutations of its next `2d`
indices. Then `|A| ≤ 4^d |S_{2d} A|`. Indices beyond the first `3d` are untouched. -/
theorem solution {n k d : ℕ} (hk : 3 * d ≤ k) (A : FunctionalInequalities.Analysis.Tensor.Coord n k)
    (h₁ : ∀ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside (FunctionalInequalities.Analysis.Tensor.slots k 0 d), FunctionalInequalities.Analysis.Tensor.slotRep n k σ A = A)
    (h₂ : ∀ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside (FunctionalInequalities.Analysis.Tensor.slots k d (3 * d)), FunctionalInequalities.Analysis.Tensor.slotRep n k σ A = A) :
    ‖A‖ ≤ (4 : ℝ) ^ d * ‖FunctionalInequalities.Analysis.Tensor.symmetrize n k (2 * d) A‖ := by
    change
      ‖A‖ ≤ (4 : ℝ) ^ d *
        ‖FunctionalInequalities.Analysis.Tensor.blockAverage (FunctionalInequalities.Analysis.Tensor.slotRep n k) (FunctionalInequalities.Analysis.Tensor.slots k 0 (2 * d)) A‖
    have hAcard : (FunctionalInequalities.Analysis.Tensor.slots k 0 d).card = d := by
      rw [FunctionalInequalities.Analysis.Tensor.card_slots_408915f (k := k) (a := 0) (b := d) (by omega)]
      omega
    have hBcard : (FunctionalInequalities.Analysis.Tensor.slots k d (3 * d)).card = 2 * d := by
      rw [FunctionalInequalities.Analysis.Tensor.card_slots_408915f (k := k) (a := d) (b := 3 * d) hk]
      omega
    have hQcard : (FunctionalInequalities.Analysis.Tensor.slots k 0 (2 * d)).card = 2 * d := by
      rw [FunctionalInequalities.Analysis.Tensor.card_slots_408915f (k := k) (a := 0) (b := 2 * d) (by omega)]
      omega
    have hdis : Disjoint (FunctionalInequalities.Analysis.Tensor.slots k 0 d) (FunctionalInequalities.Analysis.Tensor.slots k d (3 * d)) := by
      refine Finset.disjoint_left.2 ?_
      intro x hx₁ hx₂
      simp [FunctionalInequalities.Analysis.Tensor.slots] at hx₁ hx₂
      omega
    have hAQ : FunctionalInequalities.Analysis.Tensor.slots k 0 d ⊆ FunctionalInequalities.Analysis.Tensor.slots k 0 (2 * d) := by
      intro x hx
      simp [FunctionalInequalities.Analysis.Tensor.slots] at hx ⊢
      omega
    have hQ : FunctionalInequalities.Analysis.Tensor.slots k 0 (2 * d) ⊆ FunctionalInequalities.Analysis.Tensor.slots k 0 d ∪ FunctionalInequalities.Analysis.Tensor.slots k d (3 * d) := by
      intro x hx
      simp [FunctionalInequalities.Analysis.Tensor.slots] at hx ⊢
      by_cases h : x.val < d
      · left
        omega
      · right
        omega
    exact
      FunctionalInequalities.Analysis.Tensor.norm_le_four_pow_mul_norm_blockAverage_408915f
        (ρ := FunctionalInequalities.Analysis.Tensor.slotRep n k) (A := FunctionalInequalities.Analysis.Tensor.slots k 0 d) (B := FunctionalInequalities.Analysis.Tensor.slots k d (3 * d))
        (Q := FunctionalInequalities.Analysis.Tensor.slots k 0 (2 * d)) (d := d)
        hAcard hBcard hdis hAQ hQ hQcard A h₁ h₂
