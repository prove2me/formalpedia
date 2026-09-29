-- Prove2me | solution 1 for Erdos146.pairChildArrayEntropy_empirical_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:22:24.944526+00:00
-- url     : https://prove2.me/submissions/c489c29e-334a-420a-864a-d273026e9eeb

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.RCLike.Basic
import Theorems.Thm_Erdos146_pairCoordinateConditionalEntropy_empirical_bound

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    pairChildArrayEntropy parents children ≤
      kappa +
        logTwo 3 *
          pairChildArrayAverageDisagreement hparents parents children +
        (pairChildArrayEntropyPotential children -
          pairParentArrayEntropyPotential parents) / 2 +
        empiricalEntropyError parentCount := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have hsum :
      (∑ coordinate : Fin dimension,
        pairCoordinateConditionalEntropy parents children coordinate) ≤
      ∑ coordinate : Fin dimension,
        (kappa +
          logTwo 3 *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount) := by
    apply Finset.sum_le_sum
    intro coordinate _
    exact pairCoordinateConditionalEntropy_empirical_bound
      hparents parents children coordinate
  have hnormalized :=
    (div_le_div_iff_of_pos_right hdimension_real).mpr hsum
  change pairChildArrayEntropy parents children ≤ _ at hnormalized
  let disagreementSum : ℝ :=
    ∑ coordinate : Fin dimension,
      empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega)
          parents children coordinate)
  let childEntropySum : ℝ :=
    ∑ coordinate : Fin dimension,
      binaryEntropy
        ((pairChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 2 : ℝ))
  let parentEntropySum : ℝ :=
    ∑ coordinate : Fin dimension,
      binaryEntropy
        ((pairParentCoordinateOneCount parents coordinate : ℝ) /
          (parentCount : ℝ))
  have hentropy_sum :
      (∑ coordinate : Fin dimension,
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2) =
        (childEntropySum - parentEntropySum) / 2 := by
    dsimp [childEntropySum, parentEntropySum]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  have hsum_formula :
      (∑ coordinate : Fin dimension,
        (kappa +
          logTwo 3 *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount)) =
        (dimension : ℝ) * kappa +
          logTwo 3 * disagreementSum +
          (childEntropySum - parentEntropySum) / 2 +
          (dimension : ℝ) * empiricalEntropyError parentCount := by
    calc
      (∑ coordinate : Fin dimension,
        (kappa +
          logTwo 3 *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount)) =
        (∑ _coordinate : Fin dimension, kappa) +
          (∑ coordinate : Fin dimension,
            logTwo 3 *
              empiricalAverageDisagreement parentCount
                (pairParentCoordinateOneCount parents coordinate)
                (pairCoordinateKernel (by omega)
                  parents children coordinate)) +
          (∑ coordinate : Fin dimension,
            (binaryEntropy
                ((pairChildCoordinateOneCount children coordinate : ℝ) /
                  (parentCount.choose 2 : ℝ)) -
              binaryEntropy
                ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                  (parentCount : ℝ))) / 2) +
          (∑ _coordinate : Fin dimension,
            empiricalEntropyError parentCount) := by
            simp only [Finset.sum_add_distrib]
      _ = (dimension : ℝ) * kappa +
          logTwo 3 * disagreementSum +
          (childEntropySum - parentEntropySum) / 2 +
          (dimension : ℝ) * empiricalEntropyError parentCount := by
        rw [hentropy_sum]
        dsimp [disagreementSum]
        rw [← Finset.mul_sum]
        simp [nsmul_eq_mul]
  calc
    pairChildArrayEntropy parents children ≤
      (∑ coordinate : Fin dimension,
        (kappa +
          logTwo 3 *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount)) /
            (dimension : ℝ) := hnormalized
    _ = kappa +
        logTwo 3 *
          pairChildArrayAverageDisagreement hparents parents children +
        (pairChildArrayEntropyPotential children -
          pairParentArrayEntropyPotential parents) / 2 +
        empiricalEntropyError parentCount := by
      change
        (∑ coordinate : Fin dimension,
          (kappa +
            logTwo 3 *
              empiricalAverageDisagreement parentCount
                (pairParentCoordinateOneCount parents coordinate)
                (pairCoordinateKernel (by omega)
                  parents children coordinate) +
            (binaryEntropy
                ((pairChildCoordinateOneCount children coordinate : ℝ) /
                  (parentCount.choose 2 : ℝ)) -
              binaryEntropy
                ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                  (parentCount : ℝ))) / 2 +
            empiricalEntropyError parentCount)) /
              (dimension : ℝ) =
          kappa +
            logTwo 3 * (disagreementSum / (dimension : ℝ)) +
            (childEntropySum / (dimension : ℝ) -
              parentEntropySum / (dimension : ℝ)) / 2 +
            empiricalEntropyError parentCount
      rw [hsum_formula]
      field_simp [hdimension_real.ne']
