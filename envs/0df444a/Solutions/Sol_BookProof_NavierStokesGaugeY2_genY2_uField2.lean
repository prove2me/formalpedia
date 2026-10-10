-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.genY2_uField2
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:30.205566+00:00
-- url     : https://prove2.me/submissions/08e96162-58ee-4fd0-9c50-f5ce1fc3abe5

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.genY2_uField2
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Theorems.Thm_BookProof_NavierStokesGaugeY2_uField2_pderiv_y
import Theorems.Thm_BookProof_NavierStokesGaugeY2_uField2_pderiv_u
import Theorems.Thm_BookProof_NavierStokesGaugeY2_uField2_pderiv_uD
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY


private theorem genY2_apply (j : Fin 3) (p : NSAlg) :
    genY2 j p = pderiv (NSVar.y j) p
      - (∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.u i) p)
      - ∑ i : Fin 3, X (NSVar.uL i) * pderiv (NSVar.uD i j) p := by
  simp [genY2]

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 3) : genY2 j (uField2 i) = 0 := by

  rw [genY2_apply, uField2_pderiv_y,
    Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => by
      rw [uField2_pderiv_u m i] :
      ∀ m ∈ Finset.univ, X (NSVar.uD m j) * pderiv (NSVar.u m) (uField2 i)
        = X (NSVar.uD m j) * (if m = i then 1 else 0)),
    Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => by
      rw [uField2_pderiv_uD m j i] :
      ∀ m ∈ Finset.univ, X (NSVar.uL m) * pderiv (NSVar.uD m j) (uField2 i)
        = X (NSVar.uL m) * (if m = i then X (NSVar.y j) else 0))]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq' Finset.univ i,
    if_pos (Finset.mem_univ i), uDField]
  ring
