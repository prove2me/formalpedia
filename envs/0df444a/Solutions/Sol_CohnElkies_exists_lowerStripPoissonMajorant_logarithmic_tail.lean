-- Prove2me | solution 1 for CohnElkies.exists_lowerStripPoissonMajorant_logarithmic_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/8e99e04b-606e-4922-8308-3a7b56c2e5a1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerStripPoissonMajorant_dimension_neg
import Theorems.Thm_CohnElkies_exists_lowerStripPoissonMajorant_positive_logarithmic_tail

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {c σ : ℝ} (hc : 0 < c)
    (hσ : 0 ≤ σ) (hσone : σ < 1) :
    ∃ A B κ : ℝ, 0 < A ∧ 0 < B ∧ 0 < κ ∧
      ∀ d : ℕ, 2 ≤ d →
        ∀ S : ℝ, B ≤ |S| →
          lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) ≤
              -κ * ((d : ℝ) / 2) * Real.log (|S| / A) := by
  obtain ⟨A, B, κ, hA, hB, hκ, htail⟩ :=
    exists_lowerStripPoissonMajorant_positive_logarithmic_tail
      hc hσ hσone
  refine ⟨A, B, κ, hA, hB, hκ, ?_⟩
  intro d hd S hS
  by_cases hnonneg : 0 ≤ S
  · rw [abs_of_nonneg hnonneg] at hS ⊢
    exact htail d hd S hS
  · have hnegative : S < 0 := lt_of_not_ge hnonneg
    have habs : |S| = -S := abs_of_neg hnegative
    have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
    have hnegS : B ≤ -S := by simpa [habs] using! hS
    have htailneg := htail d hd (-S) hnegS
    have harg :
        ((d : ℝ) / 2) * S =
          -(((d : ℝ) / 2) * (-S)) := by
      ring
    calc
      lowerStripPoissonMajorant ((d : ℝ) / 2)
          (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) =
        lowerStripPoissonMajorant ((d : ℝ) / 2)
          (c * Real.sqrt d) σ
            (-(((d : ℝ) / 2) * (-S))) := by
          rw [harg]
      _ = lowerStripPoissonMajorant ((d : ℝ) / 2)
          (c * Real.sqrt d) σ
            (((d : ℝ) / 2) * (-S)) :=
          lowerStripPoissonMajorant_dimension_neg
            hdpos (c * Real.sqrt d) σ
              (((d : ℝ) / 2) * (-S))
      _ ≤ -κ * ((d : ℝ) / 2) *
          Real.log ((-S) / A) := htailneg
      _ = -κ * ((d : ℝ) / 2) *
          Real.log (|S| / A) := by
          rw [habs]
end CohnElkies
