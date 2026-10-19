-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.dGamma_inner_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:26:33.380198+00:00
-- url     : https://prove2.me/submissions/c9bcd47d-3806-480c-8d2a-f35b90e15f37

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.dGamma_inner_eq_integral
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_confEnergy_eq_integral
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_inner_self
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock



open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure Ω) (w : Ω → ℝ) (dens : M → Ω → ℝ)
    (hint : ∀ m, Integrable (fun ξ => w ξ * dens m ξ) μ) (v : FockDom M) :
    (inner ℂ ((v : FockL2 M)) ((dGamma (symbolOfIntegral μ w dens) v : FockDom M) : FockL2 M)
        : ℂ).re
      = ∫ ξ, w ξ * (inner ℂ ((v : FockL2 M))
          ((numberDensityOp dens ξ v : FockDom M) : FockL2 M) : ℂ).re ∂μ := by

  classical
  have hleft : (inner ℂ ((v : FockL2 M))
      ((dGamma (symbolOfIntegral μ w dens) v : FockDom M) : FockL2 M) : ℂ).re
      = ∑ n ∈ v.2.toFinset, confEnergy (symbolOfIntegral μ w dens) n
          * ‖((v : FockL2 M) : Conf M → ℂ) n‖ ^ 2 := by
    rw [dGamma, lpDiag_inner_self, Complex.ofReal_re]
  have hright : ∀ ξ : Ω, (inner ℂ ((v : FockL2 M))
      ((numberDensityOp dens ξ v : FockDom M) : FockL2 M) : ℂ).re
      = ∑ n ∈ v.2.toFinset, confDensity dens n ξ * ‖((v : FockL2 M) : Conf M → ℂ) n‖ ^ 2 := by
    intro ξ
    rw [numberDensityOp, lpDiag_inner_self, Complex.ofReal_re]
  rw [hleft]
  have hfun : (fun ξ => w ξ * (inner ℂ ((v : FockL2 M))
      ((numberDensityOp dens ξ v : FockDom M) : FockL2 M) : ℂ).re)
      = fun ξ => ∑ n ∈ v.2.toFinset,
          ‖((v : FockL2 M) : Conf M → ℂ) n‖ ^ 2 * (w ξ * confDensity dens n ξ) := by
    funext ξ
    rw [hright ξ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hintn : ∀ n : Conf M, Integrable (fun ξ => w ξ * confDensity dens n ξ) μ := by
    intro n
    have : (fun ξ => w ξ * confDensity dens n ξ)
        = fun ξ => ∑ m ∈ n.support, (n m : ℝ) * (w ξ * dens m ξ) := by
      funext ξ
      simp only [confDensity, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [this]
    exact integrable_finset_sum _ fun m _ => (hint m).const_mul _
  rw [hfun, integral_finset_sum _ fun n _ => ((hintn n).const_mul _)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, ← confEnergy_eq_integral μ w dens hint n]
  ring
