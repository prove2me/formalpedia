-- Prove2me | solution 1 for FD1D.potentialRemainder_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:09.930816+00:00
-- url     : https://prove2.me/submissions/61008cf5-47b6-46de-8213-4187bc038037

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
import Theorems.Thm_FD1D_potentialRemainder_nonneg
import Theorems.Thm_FD1D_potentialRemainder_le_sum_hazardEnergy
import Theorems.Thm_FD1D_sum_hazardEnergy_le_depth_mul

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {L : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    {q h : ∀ d, DyadicNode d → ℝ}
    (ha : 0 < a)
    (hq0 : ∀ d v, 0 ≤ q d v)
    (hq1 : ∀ d v, q d v ≤ 1)
    (hmajor : ∀ d v,
      nodeMass d v ≤ ((N d v : ℝ) + a) * h d v)
    (hmono : Monotone (hazardEnergy h)) :
    0 ≤ potentialRemainder L a N q ∧
      potentialRemainder L a N q ≤
        ∑ d ∈ Finset.range L, hazardEnergy h (d + 1) ∧
      (∑ d ∈ Finset.range L, hazardEnergy h (d + 1)) ≤
        (L : ℝ) * hazardEnergy h L := by
  exact ⟨potentialRemainder_nonneg ha hq1,
    potentialRemainder_le_sum_hazardEnergy ha hq0 hq1 hmajor,
    sum_hazardEnergy_le_depth_mul hmono⟩
end FD1D
