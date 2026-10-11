-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_eq_sum_numberOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:26:17.992983+00:00
-- url     : https://prove2.me/submissions/9ad0020e-e4cc-4af8-b002-b861063b306b

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_eq_sum_numberOp
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_numberOp_basis
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_numberDensityOp_basis
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock



open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution (dens : M → Ω → ℝ) (ξ : Ω) {n : Conf M} {S : Finset M}
    (hS : n.support ⊆ S) :
    numberDensityOp dens ξ (fockBasis n)
      = ∑ m ∈ S, ((dens m ξ : ℝ) : ℂ) • numberOp m (fockBasis n) := by

  have h : confDensity dens n ξ = ∑ m ∈ S, (n m : ℝ) * dens m ξ :=
    Finset.sum_subset hS fun m _ hm => by
      have hn : n m = 0 := by simpa using hm
      simp [hn]
  rw [numberDensityOp_basis, h]
  simp only [numberOp_basis, smul_smul, ← Complex.ofReal_mul, ← Finset.sum_smul,
    ← Complex.ofReal_sum]
  congr 2
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _
