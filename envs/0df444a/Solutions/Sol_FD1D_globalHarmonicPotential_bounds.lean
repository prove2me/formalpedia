-- Prove2me | solution 1 for FD1D.globalHarmonicPotential_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:36.56828+00:00
-- url     : https://prove2.me/submissions/68882fcf-bb0f-4e8b-8074-a89fc6128646

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
import Theorems.Thm_FD1D_globalHarmonicPotential_nonneg
import Theorems.Thm_FD1D_globalHarmonicPotential_le_log_one_add

set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {L m : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    (ha : 0 < a) (hN : ∀ d v, N d v ≤ m) :
    0 ≤ globalHarmonicPotential L a N ∧
      globalHarmonicPotential L a N ≤
        Real.log (1 + (m : ℝ) / a) :=
  ⟨globalHarmonicPotential_nonneg ha,
    globalHarmonicPotential_le_log_one_add ha hN⟩
end FD1D
