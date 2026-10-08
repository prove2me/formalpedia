-- Prove2me | solution 1 for CHMSPricing.SpmMatroid.sum_servProb_le_rank
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:32:14.957365+00:00
-- url     : https://prove2.me/submissions/6e6c73ac-0259-48a0-ab26-7c5747c29982

import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Mechanism

set_option autoImplicit false

namespace E657aa78

open MeasureTheory CHMSPricing.SpmMatroid

theorem law_univ (D : ValueDist) : D.law Set.univ = 1 := by
  unfold ValueDist.law
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : IntegrableOn D.f (Set.Icc D.lo D.hi) volume := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le D.lo_lt_hi.le).1 D.f_intervalIntegrable
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc D.lo D.hi)] D.f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (D.f_pos x hx).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le D.lo_lt_hi.le, D.f_integral, ENNReal.ofReal_one]

instance lawProb (D : ValueDist) : IsProbabilityMeasure D.law := ⟨law_univ D⟩

theorem law_ae_mem (D : ValueDist) : ∀ᵐ x ∂D.law, x ∈ Set.Icc D.lo D.hi := by
  unfold ValueDist.law
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

theorem prior_ae_typeSpace {ι : Type*} [Fintype ι] (D : ι → ValueDist) :
    ∀ᵐ v ∂(prior D), v ∈ typeSpace D := by
  unfold prior typeSpace
  have : ∀ i, ∀ᵐ v ∂(Measure.pi (fun i => (D i).law)), v i ∈ Set.Icc (D i).lo (D i).hi :=
    fun i => (Measure.quasiMeasurePreserving_eval (fun i => (D i).law) i).ae (law_ae_mem (D i))
  filter_upwards [ae_all_iff.2 this] with v hv
  exact fun i _ => hv i

instance priorProb {ι : Type*} [Fintype ι] (D : ι → ValueDist) :
    IsProbabilityMeasure (prior D) := by
  unfold prior; infer_instance

end E657aa78

open CHMSPricing.SpmMatroid MeasureTheory in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (J : SetSystem ι) (M : Mechanism ι)
    (hfeas : ∀ v ∈ typeSpace D, J.Feasible (M.alloc v))
    (hmeas : ∀ i, MeasurableSet {v | i ∈ M.alloc v}) (S : Finset ι) :
    ∑ i ∈ S, servProb D M i ≤ (J.rank S : ℝ) := by
  classical
  have key : ∑ i ∈ S, prior D {v | i ∈ M.alloc v} ≤ (J.rank S : ENNReal) := by
    have h1 : ∑ i ∈ S, prior D {v | i ∈ M.alloc v}
        = ∫⁻ v, ∑ i ∈ S, ({v | i ∈ M.alloc v} : Set (ι → ℝ)).indicator 1 v ∂(prior D) := by
      rw [lintegral_finsetSum _ (fun i _ => (measurable_one.indicator (hmeas i)))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [lintegral_indicator_one (hmeas i)]
    rw [h1]
    calc ∫⁻ v, ∑ i ∈ S, ({v | i ∈ M.alloc v} : Set (ι → ℝ)).indicator 1 v ∂(prior D)
        ≤ ∫⁻ _, (J.rank S : ENNReal) ∂(prior D) := by
          apply lintegral_mono_ae
          filter_upwards [E657aa78.prior_ae_typeSpace D] with v hv
          have hsum : ∑ i ∈ S, ({v | i ∈ M.alloc v} : Set (ι → ℝ)).indicator (1 : (ι → ℝ) → ENNReal) v
              = ((S.filter (fun i => i ∈ M.alloc v)).card : ENNReal) := by
            simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
            rw [Finset.sum_boole]
          rw [hsum]
          have hT : J.Feasible (S.filter (fun i => i ∈ M.alloc v)) :=
            J.feasible_mono (fun x hx => (Finset.mem_filter.1 hx).2) (hfeas v hv)
          have hle : (S.filter (fun i => i ∈ M.alloc v)).card ≤ J.rank S := by
            unfold SetSystem.rank
            exact Finset.le_sup (f := Finset.card)
              (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.filter_subset _ _), hT⟩)
          exact_mod_cast hle
      _ = (J.rank S : ENNReal) := by simp
  unfold servProb
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
  have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) key
  simpa using this
