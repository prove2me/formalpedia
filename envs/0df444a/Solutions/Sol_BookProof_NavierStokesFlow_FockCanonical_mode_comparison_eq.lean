-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.mode_comparison_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T09:48:04.059332+00:00
-- url     : https://prove2.me/submissions/ce43a94d-d106-48db-ac44-7646aa05e178

-- Generated from ChapterNavierStokesFockCanonical.lean — solution of BookProof.NavierStokesFlow.FockCanonical.mode_comparison_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_sq_diff
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_sqrt_half_sq
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode

variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (hκ : 0 ≤ κ i) :
    (mom κ i).comp (mom κ i) + (drift κ i).comp (drift κ i)
      = (κ i : ℂ) • ((cre i).comp (ann i) + (ann i).comp (cre i)) := by

  have h1 : (mom κ i).comp (mom κ i)
      = (-((Real.sqrt (κ i / 2) : ℂ) * (Real.sqrt (κ i / 2) : ℂ))) •
        (cre i - ann i).comp (cre i - ann i) := by
    simp only [mom, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    congr 1
    ring_nf
    rw [Complex.I_sq]
    ring
  have h2 : (drift κ i).comp (drift κ i)
      = ((Real.sqrt (κ i / 2) : ℂ) * (Real.sqrt (κ i / 2) : ℂ)) •
        (cre i + ann i).comp (cre i + ann i) := by
    simp only [drift, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  have hexp : (cre i + ann i).comp (cre i + ann i)
      = (cre i - ann i).comp (cre i - ann i)
        + (2 : ℂ) • ((cre i).comp (ann i) + (ann i).comp (cre i)) := by
    rw [← sq_diff i]
    abel
  rw [h1, h2, sqrt_half_sq i hκ, hexp]
  module
