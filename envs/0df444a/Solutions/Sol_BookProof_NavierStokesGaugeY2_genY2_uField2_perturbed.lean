-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T12:01:17.543016+00:00
-- url     : https://prove2.me/submissions/5aa90293-6d04-4623-80da-8567f19d41c3

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Theorems.Thm_BookProof_NavierStokesGaugeY2_genY2_leibniz
import Theorems.Thm_BookProof_NavierStokesGaugeY2_genY2_uField2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY


private theorem genY2_apply (j : Fin 3) (p : NSAlg) :
    genY2 j p = pderiv (NSVar.y j) p
      - (∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.u i) p)
      - ∑ i : Fin 3, X (NSVar.uL i) * pderiv (NSVar.uD i j) p := by
  simp [genY2]
@[simp] private theorem genY2_C (j : Fin 3) (c : ℂ) : genY2 j (C c) = 0 := by
  simp [genY2_apply]

/-! The platform's published `Def_ChapterNavierStokesGaugeY2` carries only the
four `def`s (`uField2`, `uDField`, `genY2`, `nsSymbol2`) and none of the
`genY2_*` equations, so `genY2_X_y` must be restated locally as `private`
(the §2.29-7 inline-helper pattern). -/

@[simp] private theorem genY2_X_y (j m : Fin 3) :
    genY2 j (X (NSVar.y m)) = if j = m then 1 else 0 := by
  by_cases h : j = m
  · subst h; simp [genY2_apply, pderiv_X]
  · simp [genY2_apply, pderiv_X, h, Ne.symm h]

set_option maxHeartbeats 1000000 in

theorem solution (i j : Fin 3) (c : ℂ) :
    genY2 j (uField2 i + C c * (X (NSVar.y j) * X (NSVar.y j)))
      = C c * (2 * X (NSVar.y j)) := by
  rw [map_add, genY2_uField2, zero_add, genY2_leibniz, genY2_C, genY2_leibniz, genY2_X_y,
    if_pos rfl]
  ring
