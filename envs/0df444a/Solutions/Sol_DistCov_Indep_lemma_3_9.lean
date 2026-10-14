-- Prove2me | solution 1 for DistCov.Indep.lemma_3_9
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T23:31:11.297875+00:00
-- url     : https://prove2.me/submissions/994b2027-1ebb-4c68-bc5f-e3a969a6532c

import Theorems.Thm_DistCov_Indep_schoenberg_embedding
import Theorems.Thm_DistCov_Indep_proposition_3_1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
open DistCov.Indep
namespace DistCovM1
abbrev E := L2N

def coord (n : ℕ) : ℝ →ₗᵢ[ℝ] E :=
  (lp.lsingle (E := fun _ : ℕ => ℝ) 2 n).toLinearIsometry
    (by exact lp.isometry_single (E := fun _ : ℕ => ℝ) (p := 2) n)

lemma ortho : OrthogonalFamily ℝ (fun _ : ℕ => ℝ) (fun n => coord (n+1)) := by
  intro i j hij a b
  change inner ℝ (lp.single 2 (i+1) a : E) (lp.single 2 (j+1) b : E) = 0
  rw [lp.inner_single_left, lp.coeFn_single, Pi.single_eq_of_ne (by omega)]
  simp

def shift : E →ₗᵢ[ℝ] E := ortho.linearIsometry

def eval0 : E →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 0

def e0 : E := lp.single 2 0 (1 : ℝ)

lemma shift_zero (u : E) : eval0 (shift u) = 0 := by
  have h := eval0.hasSum (ortho.hasSum_linearIsometry u)
  have hz (n : ℕ) : eval0 (coord (n+1) (u n)) = 0 := by
    change (lp.single 2 (n+1) (u n) : E) 0 = 0
    simp [lp.coeFn_single, Pi.single_eq_of_ne]
  simp only [hz] at h
  exact h.unique (by simp : HasSum (fun _ : ℕ => (0 : ℝ)) 0)

lemma e0_zero : eval0 e0 = 1 := by
  change (lp.single 2 0 (1 : ℝ) : E) 0 = 1
  simp

section Embedding
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


end Embedding

section Main
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

def augmented (ϕ : X → E) (x : X) : E := shift (ϕ x) + e0

lemma augmented_embedding (ϕ : X → E) (hϕ : IsNegTypeEmbedding ϕ) :
    IsNegTypeEmbedding (augmented ϕ) := by
  intro x y
  have he : augmented ϕ x - augmented ϕ y = shift (ϕ x - ϕ y) := by
    simp only [augmented, map_sub]
    abel
  rw [he, shift.norm_map]
  exact hϕ x y

lemma augmented_bary (ϕ : X → E) (hϕ : IsNegTypeEmbedding ϕ)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : FiniteFirstMoment μ) :
    bary (augmented ϕ) μ = shift (bary ϕ μ) + μ.real Set.univ • e0 := by
  have hi := embedding_integrable ϕ hϕ μ hμ
  have hs : Integrable (fun x => shift (ϕ x)) μ := shift.toContinuousLinearMap.integrable_comp hi
  have hc := shift.toContinuousLinearMap.integral_comp_comm hi
  change (∫ x, shift (ϕ x) ∂μ) = shift (∫ x, ϕ x ∂μ) at hc
  unfold bary augmented
  rw [integral_add hs (integrable_const _), hc, integral_const]

lemma firstMoment_normalized (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : FiniteFirstMoment μ) : FiniteFirstMoment ((μ Set.univ)⁻¹ • μ) := by
  obtain ⟨o,ho⟩ := hμ
  exact ⟨o, ho.to_average⟩

lemma finite_bary_inj_of_mass (ϕ : X → E) (hinj : BaryInjProb ϕ)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : FiniteFirstMoment μ) (hν : FiniteFirstMoment ν)
    (hmass : μ Set.univ = ν Set.univ) (hb : bary ϕ μ = bary ϕ ν) : μ = ν := by
  by_cases hzero : μ Set.univ = 0
  · have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.mp hzero
    have hν0 : ν = 0 := Measure.measure_univ_eq_zero.mp (hmass ▸ hzero)
    rw [hμ0,hν0]
  · haveI : NeZero μ := ⟨fun he => hzero (by simp [he])⟩
    haveI : NeZero ν := ⟨fun he => hzero (by simpa [he] using hmass)⟩
    have he := hinj ((μ Set.univ)⁻¹ • μ) ((ν Set.univ)⁻¹ • ν)
      inferInstance inferInstance (firstMoment_normalized μ hμ) (firstMoment_normalized ν hν)
      (by simp only [bary, integral_smul_measure, hmass]; exact congrArg _ hb)
    have hf := congrArg (fun m : Measure X => μ Set.univ • m) he
    simpa only [smul_smul, ← hmass, ENNReal.mul_inv_cancel hzero (measure_ne_top μ _),
      one_smul] using hf

lemma augmented_inj (ϕ : X → E) (hϕ : IsNegTypeEmbedding ϕ) (hinj : BaryInjProb ϕ) :
    BaryInjM1 (augmented ϕ) := by
  intro μ ν hμ hν hm hn hb
  letI := hμ
  letI := hν
  rw [augmented_bary ϕ hϕ μ hm, augmented_bary ϕ hϕ ν hn] at hb
  have hr := congrArg eval0 hb
  simp only [map_add, map_smul, shift_zero, e0_zero, smul_eq_mul, mul_one, zero_add] at hr
  have hmass : μ Set.univ = ν Set.univ := by
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp hr
  have hs : shift (bary ϕ μ) = shift (bary ϕ ν) := by
    rw [hr] at hb
    exact add_right_cancel hb
  exact finite_bary_inj_of_mass ϕ hinj μ ν hm hn hmass (shift.injective hs)
end Main
end DistCovM1

theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (h : StrongNegType X) :
    ∃ ϕ : X → L2N, IsNegTypeEmbedding ϕ ∧ BaryInjM1 ϕ := by
  obtain ⟨ϕ,hϕ⟩ := schoenberg_embedding.mp h.1
  have hinj := (proposition_3_1 ϕ hϕ).mp h
  exact ⟨DistCovM1.augmented ϕ, DistCovM1.augmented_embedding ϕ hϕ,
    DistCovM1.augmented_inj ϕ hϕ hinj⟩

#print axioms solution
