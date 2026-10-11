-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:25:34.173063+00:00
-- url     : https://prove2.me/submissions/ac39e2fa-1280-4f9d-951c-4d5895288af4

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.confEnergy_eq_integral
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock



open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure Ω) (w : Ω → ℝ) (dens : M → Ω → ℝ)
    (hint : ∀ m, Integrable (fun ξ => w ξ * dens m ξ) μ) (n : Conf M) :
    confEnergy (symbolOfIntegral μ w dens) n = ∫ ξ, w ξ * confDensity dens n ξ ∂μ := by

  have hsum : (fun ξ => w ξ * confDensity dens n ξ)
      = fun ξ => ∑ m ∈ n.support, (n m : ℝ) * (w ξ * dens m ξ) := by
    funext ξ
    simp only [confDensity, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hsum, integral_finset_sum _ fun m _ => ((hint m).const_mul _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_const_mul]
  rfl
