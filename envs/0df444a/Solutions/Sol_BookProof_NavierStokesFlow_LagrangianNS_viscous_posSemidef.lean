-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianNS.viscous_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:26:52.945744+00:00
-- url     : https://prove2.me/submissions/c391d925-1047-4d99-b4d5-6f6d394689a4

-- Generated from ChapterNavierStokesFlow.lean — solution of BookProof.NavierStokesFlow.LagrangianNS.viscous_posSemidef
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianNS_sum_sq_posSemidef
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianNS



open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
variable {n : ℕ} (L : LagrangianNS n)

set_option maxHeartbeats 1000000 in
theorem solution : L.viscous.PosSemidef := (sum_sq_posSemidef L.Q_herm).smul L.nu_nonneg
