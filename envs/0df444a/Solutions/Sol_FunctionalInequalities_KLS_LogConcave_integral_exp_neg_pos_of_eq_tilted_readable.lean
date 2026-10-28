-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.integral_exp_neg_pos_of_eq_tilted_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:11.045182+00:00
-- url     : https://prove2.me/submissions/cd5f288b-2505-4610-98e3-304071b6ba65

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integrable_exp_neg_of_eq_tilted_readable

noncomputable section
open MeasureTheory Set
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- A tilted law of total mass one has a positive normalizing constant `∫ e^{-W} dm`. -/
theorem solution {m : Measure V} {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) :
    0 < ∫ x, Real.exp (-W x) ∂m := by
  have hint : Integrable (fun x => Real.exp (-W x)) m :=
    FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_readable hνW
  have hm : m ≠ 0 := by
    intro hmzero
    have hzero : m.tilted (-W) = 0 := by
      simp [hmzero, Measure.tilted]
    have hνzero : (ν : Measure V) = 0 := hνW.trans hzero
    have huniv : (ν : Measure V) Set.univ = 1 := by
      simp
    rw [hνzero] at huniv
    norm_num at huniv
  have hmuniv : 0 < m Set.univ := by
    rw [pos_iff_ne_zero]
    intro hzero
    exact hm (Measure.measure_univ_eq_zero.mp hzero)
  have hsupp :
      Function.support (fun x => Real.exp (-W x)) = (Set.univ : Set V) := by
    ext x
    simp [Function.support]
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hint, hsupp]
  exact hmuniv
