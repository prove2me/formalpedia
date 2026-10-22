-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.genU_nsSymbol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:28:39.127764+00:00
-- url     : https://prove2.me/submissions/ab094088-be3d-4be7-ac31-38c0c0c65730

-- Generated from ChapterNsBrstDerivativeGauge.lean — solution of BookProof.NsBrstDerivativeGauge.genU_nsSymbol
import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Theorems.Thm_BookProof_NsBrstDerivativeGauge_genU_leibniz
import Theorems.Thm_BookProof_NsBrstDerivativeGauge_genU_uField
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NsBrstDerivativeGauge




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge
open BookProof.NavierStokesGaugeY BookProof.NavierStokesGaugeY2
open BookProof.NavierStokesGaugeY

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (nu : ℂ) (i m : Fin 3) :
    genU m (nsSymbol nu i) = X (NSVar.uD i m) := by

  have hC : genU m (C nu * X (NSVar.uL i)) = 0 := by
    simp [genU_apply, pderiv_X_of_ne (show NSVar.uL i ≠ NSVar.u m by simp)]
  have huD : ∀ j : Fin 3, genU m (X (NSVar.uD i j)) = 0 := by
    intro j
    simp [genU_apply, pderiv_X_of_ne (show NSVar.uD i j ≠ NSVar.u m by simp)]
  simp only [nsSymbol, map_sub, map_sum, hC, sub_zero, genU_leibniz, huD, mul_zero, add_zero,
    genU_uField]
  simp [ite_mul, Finset.sum_ite_eq]
