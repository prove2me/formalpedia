-- Prove2me | solution 1 for DistCov.Indep.eq_3_4
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T22:20:42.414312+00:00
-- url     : https://prove2.me/submissions/6df002bd-6999-4f48-9f78-e872170a22b4

import Definitions.Def_DistCov_Indep_Setting

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace DistCovEnergy
open DistCov.Indep
variable {X H : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma embedding_continuous (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ) : Continuous ϕ := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨ε^2, sq_pos_of_pos hε, ?_⟩
  intro y hy
  rw [dist_eq_norm]
  have hd := hϕ y x
  have hp := norm_nonneg (ϕ y - ϕ x)
  nlinarith

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma norm_sq_bound (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ) (o x : X) :
    ‖ϕ x‖^2 ≤ 2 * dist o x + 2 * ‖ϕ o‖^2 := by
  have ht := norm_add_le (ϕ x - ϕ o) (ϕ o)
  rw [sub_add_cancel] at ht
  have hd := hϕ o x
  rw [norm_sub_rev] at hd
  have ha := norm_nonneg (ϕ x - ϕ o)
  have hb := norm_nonneg (ϕ o)
  have hc := norm_nonneg (ϕ x)
  nlinarith [sq_nonneg (‖ϕ x - ϕ o‖ - ‖ϕ o‖)]

omit [SecondCountableTopology X] [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma norm_sq_integrable (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : FiniteFirstMoment μ) :
    Integrable (fun x => ‖ϕ x‖^2) μ := by
  obtain ⟨o,ho⟩ := hμ
  have hm : AEStronglyMeasurable (fun x => ‖ϕ x‖^2) μ :=
    (((embedding_continuous ϕ hϕ).norm.pow 2).stronglyMeasurable).aestronglyMeasurable
  apply ((ho.const_mul 2).add (integrable_const (2 * ‖ϕ o‖^2))).mono' hm
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ϕ x‖), Pi.add_apply] using
    norm_sq_bound ϕ hϕ o x

lemma embedding_integrable (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : FiniteFirstMoment μ) : Integrable ϕ μ := by
  apply ((norm_sq_integrable ϕ hϕ μ hμ).add (integrable_const (1 : ℝ))).mono'
    (embedding_continuous ϕ hϕ).stronglyMeasurable.aestronglyMeasurable
  filter_upwards [] with x
  change ‖ϕ x‖ ≤ ‖ϕ x‖^2 + 1
  nlinarith [sq_nonneg (‖ϕ x‖ - 1)]

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] [CompleteSpace H] in
lemma inner_prod_integrable (ϕ : X → H) (μ ν : Measure X)
    (hμ : Integrable ϕ μ) (hν : Integrable ϕ ν) :
    Integrable (fun p : X × X => inner ℝ (ϕ p.1) (ϕ p.2)) (μ.prod ν) := by
  apply (hμ.norm.mul_prod hν.norm).mono'
    (hμ.aestronglyMeasurable.comp_fst.inner hν.aestronglyMeasurable.comp_snd)
  filter_upwards [] with p
  exact norm_inner_le_norm _ _

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma inner_prod_integral (ϕ : X → H) (μ ν : Measure X) [SFinite μ] [SFinite ν]
    (hμ : Integrable ϕ μ) (hν : Integrable ϕ ν) :
    (∫ p : X × X, inner ℝ (ϕ p.1) (ϕ p.2) ∂(μ.prod ν)) =
      inner ℝ (bary ϕ μ) (bary ϕ ν) := by
  rw [integral_prod _ (inner_prod_integrable ϕ μ ν hμ hν)]
  simp_rw [integral_inner hν]
  calc
    (∫ x, inner ℝ (ϕ x) (∫ y, ϕ y ∂ν) ∂μ) =
        ∫ x, inner ℝ (∫ y, ϕ y ∂ν) (ϕ x) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => real_inner_comm _ _
    _ = _ := by rw [integral_inner hμ]; exact real_inner_comm _ _

lemma energy_expansion (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : FiniteFirstMoment μ) (hν : FiniteFirstMoment ν) :
    energy μ ν = (ν.real Set.univ) * (∫ x, ‖ϕ x‖^2 ∂μ) -
      2 * inner ℝ (bary ϕ μ) (bary ϕ ν) +
      (μ.real Set.univ) * (∫ y, ‖ϕ y‖^2 ∂ν) := by
  have hqμ := norm_sq_integrable ϕ hϕ μ hμ
  have hqν := norm_sq_integrable ϕ hϕ ν hν
  have hiμ := embedding_integrable ϕ hϕ μ hμ
  have hiν := embedding_integrable ϕ hϕ ν hν
  have hi := inner_prod_integrable ϕ μ ν hiμ hiν
  have he (p : X × X) : dist p.1 p.2 =
      ‖ϕ p.1‖^2 - 2 * inner ℝ (ϕ p.1) (ϕ p.2) + ‖ϕ p.2‖^2 := by
    rw [hϕ p.1 p.2, norm_sub_sq_real]
  unfold energy
  simp_rw [he]
  have ha := integral_add ((hqμ.comp_fst ν).sub (hi.const_mul 2)) (hqν.comp_snd μ)
  have hb := integral_sub (hqμ.comp_fst ν) (hi.const_mul 2)
  dsimp only [Pi.sub_apply] at ha hb
  rw [ha, hb, integral_const_mul, inner_prod_integral ϕ μ ν hiμ hiν]
  have hf : (∫ p : X × X, ‖ϕ p.1‖^2 ∂(μ.prod ν)) =
      ν.real Set.univ * ∫ x, ‖ϕ x‖^2 ∂μ := by
    rw [integral_prod _ (hqμ.comp_fst ν)]
    simp only [integral_const, smul_eq_mul]
    rw [integral_const_mul]
  have hg : (∫ p : X × X, ‖ϕ p.2‖^2 ∂(μ.prod ν)) =
      μ.real Set.univ * ∫ y, ‖ϕ y‖^2 ∂ν := by
    rw [integral_prod _ (hqν.comp_snd μ)]
    simp only [integral_const, smul_eq_mul]
  rw [hf,hg]

end DistCovEnergy

open DistCov.Indep
 theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ)
    (m₁ m₂ : Measure X) [IsFiniteMeasure m₁] [IsFiniteMeasure m₂]
    (h₁ : FiniteFirstMoment m₁) (h₂ : FiniteFirstMoment m₂)
    (hmass : m₁ Set.univ = m₂ Set.univ) :
    Ddiff m₁ m₂ = -2 * ‖bary ϕ m₁ - bary ϕ m₂‖ ^ 2 := by
  have he : m₁.real Set.univ = m₂.real Set.univ := by simp only [Measure.real, hmass]
  unfold Ddiff
  rw [DistCovEnergy.energy_expansion ϕ hϕ m₁ m₁ h₁ h₁,
    DistCovEnergy.energy_expansion ϕ hϕ m₁ m₂ h₁ h₂,
    DistCovEnergy.energy_expansion ϕ hϕ m₂ m₂ h₂ h₂, he,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_sub_sq_real]
  ring

#print axioms solution
