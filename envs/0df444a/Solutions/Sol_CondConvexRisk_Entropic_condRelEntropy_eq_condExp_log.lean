-- Prove2me | solution 1 for CondConvexRisk.Entropic.condRelEntropy_eq_condExp_log
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:08:28.73679+00:00
-- url     : https://prove2.me/submissions/18ae0c01-b1f1-40e4-99cd-da37cf2006f0

import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

theorem aux_cre_trim_eq {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} (hm : m ≤ mΩ)
    (Q : PG m P) : Q.1.trim hm = P.trim hm := by
  refine @Measure.ext _ m _ _ (fun s hs => ?_)
  rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs]
  exact Q.2.2.2 s hs

theorem aux_cre_change {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (Q : PG m P) (g : Ω → ENNReal) (hg : Measurable g) :
    Q.1⁻[g | m] =ᵐ[P] P⁻[fun x => Q.1.rnDeriv P x * g x | m] := by
  have : IsProbabilityMeasure Q.1 := Q.2.1
  refine ae_eq_condLExp hm P _ (measurable_condLExp _ _ _) ?_
  intro s hs
  rw [setLIntegral_rnDeriv_mul Q.2.2.1 hg.aemeasurable (hm s hs)]
  rw [← setLIntegral_trim hm (measurable_condLExp _ _ _) hs, ← aux_cre_trim_eq hm Q]
  exact setLIntegral_condLExp_trim hm Q.1 g hs

end CondConvexRisk.Entropic

open CondConvexRisk.Entropic
open MeasureTheory

theorem solution {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (Q : PG m P) :
    (P[density m P Q | m] =ᵐ[P] 1) ∧
      condRelEntropy m P Q =ᵐ[P] condExpExt m Q.1 (fun ω => Real.log (density m P Q ω)) := by
  have : IsProbabilityMeasure Q.1 := Q.2.1
  constructor
  · refine (ae_eq_condExp_of_forall_setIntegral_eq hm ?_ ?_ ?_ ?_).symm
    · exact Measure.integrable_toReal_rnDeriv
    · intro s _ _
      exact (integrable_const (1 : ℝ)).integrableOn
    · intro s hs _
      rw [show density m P Q = fun ω => (Q.1.rnDeriv P ω).toReal from rfl]
      rw [Measure.setIntegral_toReal_rnDeriv Q.2.2.1 s]
      simp [measureReal_def, Q.2.2.2 s hs]
    · exact (stronglyMeasurable_const).aestronglyMeasurable
  · have hmeas : Measurable (density m P Q) := by
      exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
    have h1 := aux_cre_change hm Q (fun x => ENNReal.ofReal (Real.log (density m P Q x)))
      (ENNReal.measurable_ofReal.comp (Real.measurable_log.comp hmeas))
    have h2 := aux_cre_change hm Q (fun x => ENNReal.ofReal (-Real.log (density m P Q x)))
      (ENNReal.measurable_ofReal.comp (Real.measurable_log.comp hmeas).neg)
    have hfin := Measure.rnDeriv_lt_top Q.1 P
    have e1 : (fun x => ENNReal.ofReal (density m P Q x * Real.log (density m P Q x)))
        =ᵐ[P] (fun x => Q.1.rnDeriv P x * ENNReal.ofReal (Real.log (density m P Q x))) := by
      filter_upwards [hfin] with x hx
      rw [show density m P Q x = (Q.1.rnDeriv P x).toReal from rfl]
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
    have e2 : (fun x => ENNReal.ofReal (-(density m P Q x * Real.log (density m P Q x))))
        =ᵐ[P] (fun x => Q.1.rnDeriv P x * ENNReal.ofReal (-Real.log (density m P Q x))) := by
      filter_upwards [hfin] with x hx
      rw [show density m P Q x = (Q.1.rnDeriv P x).toReal from rfl]
      rw [← mul_neg, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
    have k1 := condLExp_congr_ae (mΩ := m) e1
    have k2 := condLExp_congr_ae (mΩ := m) e2
    filter_upwards [h1, h2, k1, k2] with x hx1 hx2 hk1 hk2
    simp only [condRelEntropy, condExpExt]
    rw [hk1, hk2, hx1, hx2]
