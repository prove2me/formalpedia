-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.genY_uField2
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:32.411709+00:00
-- url     : https://prove2.me/submissions/14880aef-d622-48da-ba16-526f0c58c7b2

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.genY_uField2
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Theorems.Thm_BookProof_NavierStokesGaugeY2_uField2_pderiv_y
import Theorems.Thm_BookProof_NavierStokesGaugeY2_uField2_pderiv_u
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY


private theorem genY_apply (j : Fin 3) (p : NSAlg) :
    genY j p = pderiv (NSVar.y j) p - ∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.u i) p := by
  simp [genY]

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 3) :
    genY j (uField2 i) = X (NSVar.uL i) * X (NSVar.y j) := by

  rw [genY_apply, uField2_pderiv_y,
    Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => by
      rw [uField2_pderiv_u m i] :
      ∀ m ∈ Finset.univ, X (NSVar.uD m j) * pderiv (NSVar.u m) (uField2 i)
        = X (NSVar.uD m j) * (if m = i then 1 else 0))]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq' Finset.univ i,
    if_pos (Finset.mem_univ i), uDField]
  ring
