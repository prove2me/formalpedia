-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.uField2_pderiv_y
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:21.743807+00:00
-- url     : https://prove2.me/submissions/13da8075-8f3e-46ff-8065-7bcd46088912

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.uField2_pderiv_y
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Theorems.Thm_BookProof_NavierStokesGaugeY2_C_half_mul_two
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 3) :
    pderiv (NSVar.y j) (uField2 i) = uDField i j := by

  have h1 : pderiv (NSVar.y j) (X (NSVar.u i) : NSAlg) = 0 := by simp [pderiv_X]
  have h2 : ∀ m : Fin 3, pderiv (NSVar.y j) (X (NSVar.uD i m) * X (NSVar.y m) : NSAlg)
      = if j = m then X (NSVar.uD i m) else 0 := by
    intro m; rw [pderiv_mul]
    by_cases h : j = m
    · subst h; simp [pderiv_X]
    · simp [pderiv_X, h, Ne.symm h]
  have h3 : ∀ m : Fin 3,
      pderiv (NSVar.y j) (X (NSVar.uL i) * (X (NSVar.y m) * X (NSVar.y m)) : NSAlg)
        = if j = m then 2 * (X (NSVar.uL i) * X (NSVar.y m)) else 0 := by
    intro m; rw [pderiv_mul, pderiv_mul]
    by_cases h : j = m
    · subst h; simp [pderiv_X]; ring
    · simp [pderiv_X, h, Ne.symm h]
  rw [uField2, map_add, map_add, h1, map_sum, MvPolynomial.pderiv_C_mul, map_sum,
    Finset.sum_congr rfl (fun m _ => h2 m), Finset.sum_congr rfl (fun m _ => h3 m),
    Finset.sum_ite_eq Finset.univ j (fun m => X (NSVar.uD i m)),
    Finset.sum_ite_eq Finset.univ j (fun m => 2 * (X (NSVar.uL i) * X (NSVar.y m))),
    if_pos (Finset.mem_univ j), if_pos (Finset.mem_univ j), uDField, zero_add,
    ← mul_assoc, C_half_mul_two, one_mul]
