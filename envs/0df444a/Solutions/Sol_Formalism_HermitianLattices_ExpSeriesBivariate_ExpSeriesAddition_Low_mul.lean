-- Prove2me | solution 1 for Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.Low.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:38.754554+00:00
-- url     : https://prove2.me/submissions/cab5317b-ac4d-46b0-b60c-0edc17228905

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ExpSeriesBivariate Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
open Finset Formalism.G Formalism.HermitianLattices.ExpSeriesBivariate
variable {σ K : Type} [Field K] [Algebra ℚ K]
namespace Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
namespace Low
theorem _root_.solution {m k : ℕ} {x y : MvPowerSeries σ K} (hx : Low m x) (hy : Low k y) :
    Low (m + k) (x * y) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  replace hp : p.1 + p.2 = d := by
    first
    | exact _root_.Finset.mem_antidiagonal.1 hp
    | exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hdeg : p.1.degree + p.2.degree = d.degree := by
    rw [← hp]
    first
    | exact (map_add Finsupp.degree p.1 p.2).symm
    | exact (Finsupp.degree_add p.1 p.2).symm
    | (rw [Finsupp.degree_eq_weight_one, Finsupp.degree_eq_weight_one,
        Finsupp.degree_eq_weight_one]; exact (map_add _ _ _).symm)
    | (simp only [Finsupp.degree]; exact (Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)).symm)
  by_cases h1 : p.1.degree < m
  · rw [hx p.1 h1, zero_mul]
  · rw [hy p.2 (by omega), mul_zero]
end Low
end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
