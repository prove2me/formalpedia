-- Prove2me | solution 1 for BookProof.HermiteBand.Band.mono
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T01:22:23.934201+00:00
-- url     : https://prove2.me/submissions/c3d4be98-9f81-41c9-a0ca-8a9b3c4f3313

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.Band.mono
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {r M M' : ℕ}
    {C C' : ℝ} {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (hM : M ≤ M') (hC : C ≤ C')
    (h : Band T r M C g) : Band T r M' C' g := by

  intro α
  obtain ⟨f, hrep, hcard, hband, hcoef⟩ := h α
  exact ⟨f, hrep, le_trans hcard hM, hband, fun β =>
    le_trans (hcoef β) (by nlinarith [hg α.degree])⟩
