-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.lpDiag_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:18.345301+00:00
-- url     : https://prove2.me/submissions/ffe3378e-d699-481d-90a6-b5b80961e974

-- Generated from ChapterNavierStokesFockSpace.lean — solution of BookProof.NavierStokesFlow.FockOfFock.lpDiag_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_norm_lpBasis
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_basis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock









open FullEsa



variable {ι : Type*}














variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (c : ι → ℝ) (hc : ∀ C : ℝ, ∃ i, C < |c i|) :
    ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ι, ‖lpDiag c f‖ ≤ C * ‖f‖ := by

  classical
  rintro ⟨C, hC⟩
  obtain ⟨i, hi⟩ := hc C
  have hb := hC (lpBasis i)
  rw [lpDiag_basis, norm_smul, norm_lpBasis] at hb
  have hle : |c i| ≤ C := by simpa using hb
  exact absurd hi (not_lt.mpr hle)
