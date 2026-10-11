-- Prove2me | solution 1 for BookProof.NavierStokesEulerian.dirDeriv_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:16.780156+00:00
-- url     : https://prove2.me/submissions/798df415-8579-47f9-a77a-2d1029d346ea

-- Generated from ChapterNavierStokesEulerian.lean — solution of BookProof.NavierStokesEulerian.dirDeriv_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesEulerian




open BookProof.NavierStokesFlow Matrix

set_option maxHeartbeats 1000000 in
theorem solution {f : (Fin 3 → ℝ) → ℝ} {L : (Fin 3 → ℝ) →L[ℝ] ℝ} {x : Fin 3 → ℝ}
    (hf : HasFDerivAt f L x) (j : Fin 3) : dirDeriv f j x = L (evec j) := by

  have h : HasDerivAt (fun t : ℝ => x + t • evec j) (evec j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (evec j)).const_add x
  have hf_prime : HasFDerivAt f L (x + (0 : ℝ) • evec j) := by simpa using hf
  first
    | exact (hf_prime.comp_hasDerivAt 0 h).deriv
    | (simp only [dirDeriv]; exact (hf_prime.comp_hasDerivAt 0 h).deriv)
    | (simp only [dirDeriv] <;> convert (hf_prime.comp_hasDerivAt 0 h).deriv using 1
        <;> (first | rfl | simp))
