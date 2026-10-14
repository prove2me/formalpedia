-- Prove2me | solution 1 for DistCov.Converse.proposition_3_15
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T03:10:59.341736+00:00
-- url     : https://prove2.me/submissions/5f908029-62f8-434f-ab27-aa4b24424812

import Theorems.Thm_DistCov_Converse_exists_Ddiff_pos
import Theorems.Thm_DistCov_Converse_dcov_twoPointLaw
import Theorems.Thm_DistCov_Converse_exists_gamma_Ddiff_eq_zero
import Theorems.Thm_DistCov_Converse_twoPointLaw_not_isProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
open DistCov.Indep DistCov.Converse
namespace DistCovConverseRoot
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
lemma dist_integrable (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) (x : X) :
    Integrable (fun z => dist x z) μ := by
  obtain ⟨o,ho⟩ := h
  apply ((integrable_const (dist x o)).add ho).mono' (by fun_prop)
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, Pi.add_apply] using dist_triangle x o z

local notation "c" => (2 : ℝ≥0∞)⁻¹

def avg (μ ν : Measure X) : Measure X := c • (μ + ν)

instance avg_prob (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (avg μ ν) := by
  constructor
  norm_num [avg, Measure.add_apply, Measure.smul_apply, ENNReal.inv_two_add_inv_two]

lemma avg_moment (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : FiniteFirstMoment μ) (hν : FiniteFirstMoment ν) : FiniteFirstMoment (avg μ ν) := by
  obtain ⟨o, ho⟩ := hμ
  refine ⟨o, ?_⟩
  exact (integrable_add_measure.mpr ⟨ho, dist_integrable ν hν o⟩).smul_measure (by simp)

lemma dirac_moment (x : X) : FiniteFirstMoment (Measure.dirac x) := by
  exact ⟨x, integrable_dirac (by simp)⟩

lemma marg_fst (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y z : Y) : (twoPointLaw μ ν y z).map Prod.fst = avg μ ν := by
  simp [twoPointLaw, avg, Measure.map_smul, Measure.map_add, measurable_fst,
    Measure.map_fst_prod, smul_add]

lemma marg_snd (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y z : Y) : (twoPointLaw μ ν y z).map Prod.snd = avg (Measure.dirac y) (Measure.dirac z) := by
  simp [twoPointLaw, avg, Measure.map_smul, Measure.map_add, measurable_snd,
    Measure.map_snd_prod, smul_add]

instance law_prob (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (y z : Y) : IsProbabilityMeasure (twoPointLaw μ ν y z) := by
  constructor
  norm_num [twoPointLaw, Measure.add_apply, Measure.smul_apply, ENNReal.inv_two_add_inv_two]

lemma mix_probability (μ : Measure X) [IsProbabilityMeasure μ] (x : X)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : IsProbabilityMeasure (mixDirac r μ x) := by
  constructor
  simp only [mixDirac, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hr.1 (sub_nonneg.mpr hr.2)]
  simp

lemma mix_moment (μ : Measure X) [IsProbabilityMeasure μ] (hμ : FiniteFirstMoment μ)
    (x : X) (r : ℝ) : FiniteFirstMoment (mixDirac r μ x) := by
  refine ⟨x, ?_⟩
  exact integrable_add_measure.mpr
    ⟨(dist_integrable μ hμ x).smul_measure ENNReal.ofReal_ne_top,
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top⟩


lemma law_properties (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : FiniteFirstMoment μ) (hν : FiniteFirstMoment ν) (y z : Y) :
    IsProbabilityMeasure (twoPointLaw μ ν y z) ∧
      FiniteFirstMoment ((twoPointLaw μ ν y z).map Prod.fst) ∧
      FiniteFirstMoment ((twoPointLaw μ ν y z).map Prod.snd) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [marg_fst]
    exact avg_moment μ ν hμ hν
  · rw [marg_snd]
    exact avg_moment _ _ (dirac_moment y) (dirac_moment z)

lemma anchors_of_distinct_prob (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hne : μ ≠ ν) : ∃ x y : X, x ≠ y := by
  classical
  by_contra h
  push Not at h
  apply hne
  apply Measure.ext
  intro A hA
  by_cases he : A = ∅
  · simp [he]
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr he
  have hAu : A = univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    rw [← h a x]
    exact ha
  simp [hAu]

end DistCovConverseRoot

open DistCovConverseRoot

theorem solution
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (hY : ∃ y₁ y₂ : Y, y₁ ≠ y₂) :
    (¬ NegType X → ∃ θ : Measure (X × Y), IsProbabilityMeasure θ ∧
      FiniteFirstMoment (θ.map Prod.fst) ∧ FiniteFirstMoment (θ.map Prod.snd) ∧ dcov θ < 0) ∧
    (¬ StrongNegType X → ∃ θ : Measure (X × Y), IsProbabilityMeasure θ ∧
      FiniteFirstMoment (θ.map Prod.fst) ∧ FiniteFirstMoment (θ.map Prod.snd) ∧
      dcov θ = 0 ∧ ¬ IsProduct θ) := by
  classical
  obtain ⟨y₁, y₂, hy⟩ := hY
  constructor
  · intro hX
    obtain ⟨μ, ν, hprobμ, hprobν, hμ, hν, hne, hD⟩ := DistCov.Converse.exists_Ddiff_pos hX
    letI := hprobμ
    letI := hprobν
    obtain ⟨hp, hf, hs⟩ := law_properties μ ν hμ hν y₁ y₂
    refine ⟨twoPointLaw μ ν y₁ y₂, hp, hf, hs, ?_⟩
    rw [DistCov.Converse.dcov_twoPointLaw μ ν hμ hν y₁ y₂ hy]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos (dist_pos.mpr hy)) hD) (by norm_num)
  · intro hX
    have hw : ∃ μ ν : Measure X, IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
        FiniteFirstMoment μ ∧ FiniteFirstMoment ν ∧ μ ≠ ν ∧ 0 ≤ Ddiff μ ν := by
      by_cases hNT : NegType X
      · have hs : ¬ (∀ μ ν : Measure X, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
            FiniteFirstMoment μ → FiniteFirstMoment ν → Ddiff μ ν = 0 → μ = ν) :=
          fun h => hX ⟨hNT, h⟩
        push Not at hs
        obtain ⟨μ, ν, hpμ, hpν, hμ, hν, he, hne⟩ := hs
        exact ⟨μ, ν, hpμ, hpν, hμ, hν, hne, by rw [he]⟩
      · obtain ⟨μ, ν, hpμ, hpν, hμ, hν, hne, hpos⟩ := DistCov.Converse.exists_Ddiff_pos hNT
        exact ⟨μ, ν, hpμ, hpν, hμ, hν, hne, le_of_lt hpos⟩
    obtain ⟨μ, ν, hpμ, hpν, hμ, hν, hne, hD⟩ := hw
    letI := hpμ
    letI := hpν
    obtain ⟨x₁, x₂, hx⟩ := anchors_of_distinct_prob μ ν hne
    obtain ⟨γ, hγ, hz⟩ := DistCov.Converse.exists_gamma_Ddiff_eq_zero μ ν hμ hν hD x₁ x₂ hx
    have hgi : γ ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hγ.1, hγ.2⟩
    letI := mix_probability μ x₁ γ hgi
    letI := mix_probability ν x₂ γ hgi
    have hm := mix_moment μ hμ x₁ γ
    have hn := mix_moment ν hν x₂ γ
    obtain ⟨hp, hf, hs⟩ := law_properties _ _ hm hn y₁ y₂
    refine ⟨twoPointLaw (mixDirac γ μ x₁) (mixDirac γ ν x₂) y₁ y₂, hp, hf, hs, ?_, ?_⟩
    · rw [DistCov.Converse.dcov_twoPointLaw _ _ hm hn y₁ y₂ hy, hz]
      simp
    · exact DistCov.Converse.twoPointLaw_not_isProduct μ ν hμ hν hne hD x₁ x₂ hx γ hγ y₁ y₂ hy

#print axioms solution
