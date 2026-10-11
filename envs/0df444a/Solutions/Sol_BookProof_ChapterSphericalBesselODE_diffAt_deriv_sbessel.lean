-- Prove2me | solution 1 for BookProof.ChapterSphericalBesselODE.diffAt_deriv_sbessel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:45.615926+00:00
-- url     : https://prove2.me/submissions/4144a2f9-3d06-4afa-a604-f4051a885a83

-- Generated from ChapterSphericalBesselODE.lean — solution of BookProof.ChapterSphericalBesselODE.diffAt_deriv_sbessel
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_diffAt_gIter
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_diffAt_deriv_gIter
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_hasDerivAt_sbessel
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE




open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (deriv (sbessel l)) x := by

  have hEq : deriv (sbessel l) =ᶠ[nhds x]
      fun s => s ^ l * ((l : ℝ) * gIter l s / s + deriv (gIter l) s) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with s hs using (hasDerivAt_sbessel l hs).deriv
  have hdiff : DifferentiableAt ℝ
      (fun s : ℝ => s ^ l * ((l : ℝ) * gIter l s / s + deriv (gIter l) s)) x := by
    have h1 : DifferentiableAt ℝ (fun s : ℝ => s ^ l) x := (differentiable_pow l).differentiableAt
    have h2 : DifferentiableAt ℝ (fun s : ℝ => (l : ℝ) * gIter l s / s) x :=
      ((diffAt_gIter l hx).const_mul _).div differentiableAt_id hx
    exact h1.mul (h2.add (diffAt_deriv_gIter l hx))
  exact hdiff.congr_of_eventuallyEq hEq
