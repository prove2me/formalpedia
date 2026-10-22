-- Prove2me | solution 1 for GaussianMatrix.wishart_lambda_min_cdf_density_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:47:11.634155+00:00
-- url     : https://prove2.me/submissions/140de249-085b-4b08-9c5d-e74fda5076d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_wishart_lambda_min_law_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory
open scoped Matrix

open GaussianMatrix

theorem solution {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (t : ℝ)
    (ht : 0 < t) :
    (gaussianMatrix r k) {G | sMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      ≤ ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal
          (2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
              / (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))
            * x ^ (((k : ℝ) - r - 1) / 2) * Real.exp (-x / 2)) := by
  -- the Edelmann domination of the law of the smallest Wishart eigenvalue
  have hchild := wishart_lambda_min_law_le hr hrk (Set.Iic t) measurableSet_Iic
  -- `(Iic t ∩ Ioi 0) = Ioc 0 t`
  have hset : Set.Iic t ∩ Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) t := by
    ext x
    simp only [Set.mem_Iic, Set.mem_Ioi, Set.mem_Ioc]
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx2, hx1⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx2, hx1⟩
  rw [hset] at hchild
  exact hchild
