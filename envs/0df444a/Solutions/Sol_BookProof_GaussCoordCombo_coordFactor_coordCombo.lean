-- Prove2me | solution 1 for BookProof.GaussCoordCombo.coordFactor_coordCombo
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:44:02.727299+00:00
-- url     : https://prove2.me/submissions/e5399b04-f4f2-4194-8c3e-8f1d58429047

-- Generated from ChapterGaussCoordCombo.lean — solution of BookProof.GaussCoordCombo.coordFactor_coordCombo
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Theorems.Thm_BookProof_GaussCoordCombo_pderiv_coordCombo_of_ne
import Theorems.Thm_BookProof_GaussCoordCombo_gaussInt_coordCombo_sq
open BookProof.GaussCoordCombo




open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (c : ℕ → ℝ) (p K : ℕ) :
    CoordFactor i (coordCombo i c p K) (coordComboSum c p K) := ⟨fun _ hj => pderiv_coordCombo_of_ne hj c p K, fun _ hR => gaussInt_coordCombo_sq i c p K hR⟩
