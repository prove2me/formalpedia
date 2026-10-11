-- Prove2me | solution 1 for BookProof.SqueezedGaussStates.coordCombo_smul_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:46.730189+00:00
-- url     : https://prove2.me/submissions/b7ea4a2b-c248-4b56-96c0-3469f595f371

-- Generated from ChapterSqueezedGaussStates.lean — solution of BookProof.SqueezedGaussStates.coordCombo_smul_add
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
open BookProof.SqueezedGaussStates




open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (c₁ c₂ : ℕ → ℝ) (α γ : ℝ) (p K : ℕ) :
    ((α : ℝ) : ℂ) • coordCombo i c₁ p K + ((γ : ℝ) : ℂ) • coordCombo i c₂ p K
      = coordCombo i (fun k => α * c₁ k + γ * c₂ k) p K := by

  simp only [coordCombo, Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  module
