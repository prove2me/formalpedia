-- Prove2me | solution 1 for DistCov.Indep.theorem_3_11
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T23:49:32.437656+00:00
-- url     : https://prove2.me/submissions/b34fda4c-ec8a-4f1f-9dc5-59f3d621be46

import Theorems.Thm_DistCov_Indep_lemma_3_8
import Theorems.Thm_DistCov_Indep_proposition_3_7

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory
open DistCov.Indep

theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [SecondCountableTopology Y]
    (hX : StrongNegType X) (hY : StrongNegType Y)
    (θ : Measure (X × Y)) [IsProbabilityMeasure θ]
    (hμ : FiniteFirstMoment (θ.map Prod.fst)) (hν : FiniteFirstMoment (θ.map Prod.snd))
    (h : dcov θ = 0) : IsProduct θ := by
  obtain ⟨ϕ,ψ,hϕ,hψ,hpϕ,hpψ,hinj⟩ := lemma_3_8 hX hY
  haveI : IsProbabilityMeasure (θ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure (θ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have he := (proposition_3_7 ϕ ψ hϕ hψ θ hμ hν).2
  rw [h] at he
  have hn : ‖bary (tensorEmb ϕ ψ) θ -
      bary (tensorEmb ϕ ψ) ((θ.map Prod.fst).prod (θ.map Prod.snd))‖^2 = 0 := by linarith
  have hb : bary (tensorEmb ϕ ψ) θ =
      bary (tensorEmb ϕ ψ) ((θ.map Prod.fst).prod (θ.map Prod.snd)) :=
    sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  have hm : FiniteFirstMoment
      (((θ.map Prod.fst).prod (θ.map Prod.snd)).map Prod.fst) := by simpa using hμ
  have hv : FiniteFirstMoment
      (((θ.map Prod.fst).prod (θ.map Prod.snd)).map Prod.snd) := by simpa using hν
  exact hinj θ ((θ.map Prod.fst).prod (θ.map Prod.snd))
    inferInstance inferInstance hμ hν hm hv hb

#print axioms solution
