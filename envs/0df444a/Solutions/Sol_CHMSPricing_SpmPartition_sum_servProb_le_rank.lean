-- Prove2me | solution 1 for CHMSPricing.SpmPartition.sum_servProb_le_rank
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:45:09.662027+00:00
-- url     : https://prove2.me/submissions/5213e195-fe49-4c70-a3ba-aa2c7eb4de69

import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_ValueDist
import Definitions.Def_CHMSPricing_SpmPartition_SetSystem
import Definitions.Def_CHMSPricing_SpmPartition_Mechanism



namespace CHMSPricing.SpmPartition

open MeasureTheory Set

namespace RankAux

variable (D : ValueDist)

lemma f_intOn : IntegrableOn D.f (Icc D.lo D.hi) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le D.lo_lt_hi.le).1 D.f_intervalIntegrable

lemma setInt_f : ∫ x in Icc D.lo D.hi, D.f x = 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le D.lo_lt_hi.le,
    D.f_integral]

lemma law_univ : D.law univ = 1 := by
  rw [ValueDist.law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (f_intOn D), setInt_f]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (D.f_pos x hx).le

instance law_prob : IsProbabilityMeasure D.law := ⟨law_univ D⟩

lemma law_ac : D.law ≪ volume.restrict (Icc D.lo D.hi) := withDensity_absolutelyContinuous _ _

lemma law_ae_mem : ∀ᵐ x ∂D.law, x ∈ Icc D.lo D.hi :=
  law_ac D (ae_restrict_mem measurableSet_Icc)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance prior_prob (D : ι → ValueDist) : IsProbabilityMeasure (prior D) := by
  unfold prior; infer_instance

lemma ae_ts (D : ι → ValueDist) : ∀ᵐ v ∂(prior D), v ∈ typeSpace D := by
  have h1 : ∀ i, (D i).law (Icc (D i).lo (D i).hi) = 1 := by
    intro i
    rw [← prob_compl_eq_zero_iff measurableSet_Icc]
    have := law_ae_mem (D i)
    rwa [ae_iff] at this
  have h2 : prior D (typeSpace D) = 1 := by
    rw [typeSpace, prior, Measure.pi_pi]; simp [h1]
  have hm : MeasurableSet (typeSpace D) := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  rw [ae_iff]
  have := (prob_compl_eq_zero_iff hm).2 h2
  simpa [compl_def] using this

end RankAux

theorem sum_servProb_le_rank_core {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (J : SetSystem ι) (M : Mechanism ι) (hM : IsTruthful D J M)
    (S : Finset ι) :
    ∑ i ∈ S, servProb D M i ≤ (J.rank S : ℝ) := by
  classical
  have e : ∀ i, servProb D M i =
      ∫ v, {v | i ∈ M.alloc v}.indicator (fun _ => (1:ℝ)) v ∂(prior D) := by
    intro i
    rw [integral_indicator_const _ (hM.alloc_measurable i), measureReal_def, smul_eq_mul,
      mul_one, servProb]
  simp_rw [e]
  rw [← integral_finsetSum _ (fun i _ =>
    (integrable_const (1:ℝ)).indicator (hM.alloc_measurable i))]
  have : ∫ v, ((J.rank S : ℕ) : ℝ) ∂(prior D) = J.rank S := by simp
  rw [← this]
  refine integral_mono_ae (integrable_finsetSum _ (fun i _ =>
    (integrable_const (1:ℝ)).indicator (hM.alloc_measurable i))) (integrable_const _) ?_
  filter_upwards [RankAux.ae_ts D] with v hv
  have hc : ∑ i ∈ S, {v | i ∈ M.alloc v}.indicator (fun _ => (1:ℝ)) v =
      ((M.alloc v ∩ S).card : ℝ) := by
    have : M.alloc v ∩ S = S.filter (· ∈ M.alloc v) := by ext; simp [and_comm]
    rw [this, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [Set.indicator]
  rw [hc]
  have hF : J.Feasible (M.alloc v ∩ S) :=
    J.feasible_mono Finset.inter_subset_left (hM.feasible v hv)
  have : (M.alloc v ∩ S).card ≤ J.rank S := by
    unfold SetSystem.rank
    exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2
      ⟨Finset.mem_powerset.2 Finset.inter_subset_right, hF⟩)
  exact_mod_cast this

end CHMSPricing.SpmPartition

open CHMSPricing.SpmPartition


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (J : SetSystem ι) (M : Mechanism ι) (hM : IsTruthful D J M)
    (S : Finset ι) :
    ∑ i ∈ S, servProb D M i ≤ (J.rank S : ℝ) := by
  exact sum_servProb_le_rank_core D J M hM S
