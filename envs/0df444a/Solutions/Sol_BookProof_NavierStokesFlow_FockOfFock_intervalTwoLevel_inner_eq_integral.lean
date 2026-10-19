-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_inner_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:14.191303+00:00
-- url     : https://prove2.me/submissions/9b8a76a2-ff34-45a5-9647-313f0d079192

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_inner_eq_integral
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_dGamma_add
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_dGamma_inner_eq_integral
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_intervalDens_integrable
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_intervalTwoLevelSymbol_eq
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock



open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]
variable {J K : Type*} [DecidableEq J] [DecidableEq K]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {K : Type*} [DecidableEq K]

set_option maxHeartbeats 1000000 in
theorem solution (eps : K → ℝ) (v : FockOfFockDom ℕ K) :
    (inner ℂ ((v : FockOfFockL2 ℕ K))
        ((dGamma (intervalTwoLevelSymbol eps) v : FockOfFockDom ℕ K) : FockOfFockL2 ℕ K) : ℂ).re
      = (∫ ξ, extField ξ * (inner ℂ ((v : FockOfFockL2 ℕ K))
            ((numberDensityOp parcelDens ξ v : FockOfFockDom ℕ K) : FockOfFockL2 ℕ K) : ℂ).re)
        + (inner ℂ ((v : FockOfFockL2 ℕ K))
            ((dGamma (innerEnergySymbol eps) v : FockOfFockDom ℕ K) : FockOfFockL2 ℕ K)
              : ℂ).re := by

  have hint : ∀ m : ℕ × Conf K,
      Integrable (fun ξ => extField ξ * parcelDens m ξ) volume := fun m =>
    intervalDens_integrable m.1
  rw [intervalTwoLevelSymbol_eq, dGamma_add]
  simp only [LinearMap.add_apply, Submodule.coe_add, inner_add_right, Complex.add_re]
  rw [dGamma_inner_eq_integral volume extField parcelDens hint v]
