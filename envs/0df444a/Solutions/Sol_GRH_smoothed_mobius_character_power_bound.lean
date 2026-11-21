-- Prove2me | solution 1 for GRH.smoothed_mobius_character_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:05:34.41348+00:00
-- url     : https://prove2.me/submissions/a643d307-551e-4066-bfc9-b1ed315dd52d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_exponential_smoothing_of_partialSums_isBigO_rpow
import Theorems.Thm_GRH_sharp_mobius_character_power_bound
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing

open Filter Asymptotics

theorem solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (hhalf : (1/2 : ℝ) < σ) (hone : σ < 1) :
    (fun D : ℝ => OAI.ShortDraftMellin.mobiusExpSum χ D⁻¹) =O[atTop]
      (fun D : ℝ => D^σ) := by
  apply GRH.exponential_smoothing_of_partialSums_isBigO_rpow
    (fun k : ℕ => χ k * (ArithmeticFunction.moebius k : ℂ)) σ (by linarith) hone.le
  exact GRH.sharp_mobius_character_power_bound q χ σ hhalf hone
