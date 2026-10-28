-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:26:47.752662+00:00
-- url     : https://prove2.me/submissions/bce86950-5905-48cd-aa13-a2f421eb9030

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted

noncomputable section
open MeasureTheory Set
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- A tilted law of total mass one has an integrable density: `e^{-W} ∈ L¹(m)`. -/
theorem solution {m : Measure V} {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) :
    Integrable (fun x => Real.exp (-W x)) m := by
  by_contra h
  have h' : ¬ Integrable (fun x => Real.exp ((-W) x)) m := by
    intro hI
    apply h
    simpa using hI
  have hzero : m.tilted (-W) = 0 :=
    tilted_of_not_integrable h'
  have hνzero : (ν : Measure V) = 0 := by
    rw [hνW, hzero]
  have huniv : (ν : Measure V) Set.univ = 1 := by
    simp
  rw [hνzero] at huniv
  norm_num at huniv
