-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.genY_shifts_velocity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:07:15.063532+00:00
-- url     : https://prove2.me/submissions/6f0bfdc2-0c5d-4b75-ab38-149a93f3949f

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.genY_shifts_velocity
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow


private theorem genY_apply (j : Fin 3) (p : NSAlg) :
    genY j p = pderiv (NSVar.y j) p - ∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.u i) p := by
  simp [genY]

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 3) (p : NSAlg) :
    genY j (X (NSVar.u i) * p) - X (NSVar.u i) * genY j p = -(X (NSVar.uD i j) * p) := by

  have expand : ∀ m : Fin 3, X (NSVar.uD m j) * pderiv (NSVar.u m) (X (NSVar.u i) * p)
      = (if m = i then X (NSVar.uD m j) * p else 0)
        + X (NSVar.u i) * (X (NSVar.uD m j) * pderiv (NSVar.u m) p) := by
    intro m
    rw [pderiv_mul, pderiv_X, Pi.single_apply]
    simp only [NSVar.u.injEq]
    by_cases h : m = i
    · subst h; simp; ring
    · rw [if_neg (fun hh : i = m => h hh.symm), if_neg h]; ring
  have hsum : ∑ m : Fin 3, X (NSVar.uD m j) * pderiv (NSVar.u m) (X (NSVar.u i) * p)
      = X (NSVar.uD i j) * p
        + X (NSVar.u i) * ∑ m : Fin 3, X (NSVar.uD m j) * pderiv (NSVar.u m) p := by
    rw [Finset.sum_congr rfl fun m _ => expand m, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i (fun m => X (NSVar.uD m j) * p),
      if_pos (Finset.mem_univ i), Finset.mul_sum]
  rw [genY_apply, genY_apply, hsum, pderiv_mul, pderiv_X_of_ne (by simp)]
  ring
