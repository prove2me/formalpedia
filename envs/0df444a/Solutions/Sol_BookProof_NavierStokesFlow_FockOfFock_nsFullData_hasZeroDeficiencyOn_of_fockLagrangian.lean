-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.nsFullData_hasZeroDeficiencyOn_of_fockLagrangian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:53:42.655522+00:00
-- url     : https://prove2.me/submissions/678a121e-a23e-4c20-9013-21556be74277

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.nsFullData_hasZeroDeficiencyOn_of_fockLagrangian
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lagrangianFock_hasZeroDeficiencyOn
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_NSFullData_hasZeroDeficiencyOn_of_lagrangian
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock



open MeasureTheory



open FullEsa LagrangianEsa
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.FullEsa.NSFullData

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]
variable {J K : Type*} [DecidableEq J] [DecidableEq K]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (d : FullEsa.NSFullData F) (nu : ℝ)
    (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ) (cst : M → ℝ)
    (W : F ≃ₗᵢ[ℂ] FockL2 M)
    (hmap : ∀ x : d.D, W (x : F) ∈ (lagrangianFockData nu hnu p q dr force cst).D)
    (hsurj : ∀ y : (lagrangianFockData nu hnu p q dr force cst).D,
      ∃ x : d.D, W (x : F) = (y : FockL2 M))
    (hint : ∀ x : d.D, ((lagrangianFockData nu hnu p q dr force cst).hFull
        ⟨W (x : F), hmap x⟩ : FockL2 M) = W ((d.hamiltonian x : F))) :
    HasZeroDeficiencyOn d.D d.hamiltonian :=
  LagrangianEsa.NSFullData.hasZeroDeficiencyOn_of_lagrangian d
      (lagrangianFockData nu hnu p q dr force cst) W hmap hsurj hint
      (lagrangianFock_hasZeroDeficiencyOn nu hnu p q dr force cst)
