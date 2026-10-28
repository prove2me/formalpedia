-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_eq_tilted_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:16.078655+00:00
-- url     : https://prove2.me/submissions/fe41def8-0a15-4e49-a7ad-5bed8a7dbefc

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integrable_exp_neg_of_eq_tilted_readable

noncomputable section
open MeasureTheory Set
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- A tilted Haar law has full support, so its support has nonempty interior. -/
theorem solution (m : Measure V) [m.IsAddHaarMeasure] {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) :
    (interior (ν : Measure V).support).Nonempty := by
  have hint : Integrable (fun x => Real.exp (-W x)) m :=
    FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_readable hνW
  have hac : m ≪ (ν : Measure V) := by
    rw [hνW]
    exact absolutelyContinuous_tilted (by simpa using hint)
  have hsupp : (ν : Measure V).support = (Set.univ : Set V) := by
    apply Set.eq_univ_of_forall
    intro x
    apply (Measure.mem_support_iff_forall x).2
    intro U hU
    have hmU : 0 < m U := Measure.measure_pos_of_mem_nhds m hU
    exact pos_iff_ne_zero.2 fun h0 =>
      (pos_iff_ne_zero.1 hmU) (hac h0)
  rw [hsupp, interior_univ]
  exact Set.univ_nonempty
