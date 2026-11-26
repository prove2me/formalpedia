-- Prove2me | solution 1 for FD1D.globalHarmonicPotential_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:51.368676+00:00
-- url     : https://prove2.me/submissions/ac7aa53d-5127-4a2e-b9e2-69c4bf6be448

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
import Theorems.Thm_FD1D_harmonicPotential_nonneg

set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {L : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    (ha : 0 < a) :
    0 ≤ globalHarmonicPotential L a N := by
  unfold globalHarmonicPotential
  apply Finset.sum_nonneg
  intro d hd
  apply Finset.sum_nonneg
  intro v hv
  exact mul_nonneg (sq_nonneg _) (harmonicPotential_nonneg ha _)
end FD1D
