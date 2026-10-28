-- Prove2me | solution 1 for FunctionalInequalities.Energy.exists_thickening_pairwise_disjoint_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:43:21.012664+00:00
-- url     : https://prove2.me/submissions/8fa5e834-9090-4d01-a07c-70fbbfca673e

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Density

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
universe u
section Separation
variable {X : Type*} [MetricSpace X]
/-- Finitely many pairwise disjoint compact sets have one common thickening radius keeping the
thickenings pairwise disjoint. -/
theorem solution (N : ℕ) (Kc : ℕ → Set X)
    (hcomp : ∀ n, IsCompact (Kc n)) (hdisj : ∀ i j, i ≠ j → Disjoint (Kc i) (Kc j)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i < N, ∀ j < N, i ≠ j →
      Disjoint (Metric.thickening ρ (Kc i)) (Metric.thickening ρ (Kc j)) := by
  induction N with
  | zero => exact ⟨1, one_pos, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
  | succ N ih =>
    obtain ⟨ρ₁, hρ₁, hsep₁⟩ := ih
    set U : Set X := ⋃ i : Fin N, Kc (i : ℕ) with hU
    have hUcompact : IsCompact U := isCompact_iUnion fun i ↦ hcomp _
    have hdisjU : Disjoint (Kc N) U := by
      rw [hU, Set.disjoint_iUnion_right]
      intro i
      exact hdisj N i (by omega)
    obtain ⟨ρ₂, hρ₂, hsep₂⟩ := hdisjU.exists_thickenings (hcomp N) hUcompact.isClosed
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun i hi j hj hij ↦ ?_⟩
    have hsubU : ∀ k, k < N → Metric.thickening (min ρ₁ ρ₂) (Kc k) ⊆ Metric.thickening ρ₂ U := by
      intro k hk
      refine subset_trans (Metric.thickening_mono (min_le_right _ _) _) ?_
      exact Metric.thickening_subset_of_subset _ (Set.subset_iUnion (fun i : Fin N ↦ Kc i) ⟨k, hk⟩)
    have hsubN : Metric.thickening (min ρ₁ ρ₂) (Kc N) ⊆ Metric.thickening ρ₂ (Kc N) :=
      Metric.thickening_mono (min_le_right _ _) _
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | hi'
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
      · exact Disjoint.mono (Metric.thickening_mono (min_le_left _ _) _)
          (Metric.thickening_mono (min_le_left _ _) _) (hsep₁ i hi' j hj' hij)
      · subst hj'
        exact Disjoint.mono (hsubU i hi') hsubN hsep₂.symm
    · subst hi'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
      · exact Disjoint.mono hsubN (hsubU j hj') hsep₂
      · exact absurd hj'.symm hij
