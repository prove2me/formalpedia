-- Prove2me | solution 1 for DistCov.Indep.proposition_3_7
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T23:06:29.455922+00:00
-- url     : https://prove2.me/submissions/b9f79b3a-e870-49da-a1f4-f34efb9ee1bb

import Theorems.Thm_DistCov_Indep_proposition_3_5

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace TensorProduct
open DistCov.Indep
namespace DistCovTensor
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


lemma embedding_memLp (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : FiniteFirstMoment μ) : MemLp ϕ 2 μ :=
  (memLp_two_iff_integrable_sq_norm
    (embedding_continuous ϕ hϕ).stronglyMeasurable.aestronglyMeasurable).mpr
      (norm_sq_integrable ϕ hϕ μ hμ)
end Embedding

section Tensor
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

def T : H →L[ℝ] K →L[ℝ] HTensor H K :=
  (ContinuousLinearMap.compL ℝ K (H ⊗[ℝ] K) (HTensor H K)
    UniformSpace.Completion.toComplL).comp (TensorProduct.mkL ℝ H K)

lemma T_apply (x : H) (y : K) : T x y = ((x ⊗ₜ[ℝ] y : H ⊗[ℝ] K) : HTensor H K) := rfl

lemma T_norm (x : H) (y : K) : ‖T x y‖ = ‖x‖ * ‖y‖ := by
  rw [T_apply, UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul]

lemma T_inner (x x' : H) (y y' : K) :
    inner ℝ (T x y) (T x' y') = inner ℝ x x' * inner ℝ y y' := by
  rw [T_apply, T_apply, UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]

lemma T_sub_sub (x a : H) (y b : K) :
    T (x-a) (y-b) = T x y - T x b - T a y + T a b := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  abel

lemma tensor_integrable_L2 {Z : Type*} [MeasurableSpace Z] (m : Measure Z)
    {f : Z → H} {g : Z → K} (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    Integrable (fun z => T (f z) (g z)) m := by
  apply (hf.norm.integrable_mul hg.norm).mono'
    ((T (H := H) (K := K)).continuous₂.comp_aestronglyMeasurable₂ hf.1 hg.1)
  filter_upwards [] with z
  exact (T_norm (f z) (g z)).le

lemma tensor_integrable_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {f : X → H} {g : Y → K}
    (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun p : X × Y => T (f p.1) (g p.2)) (μ.prod ν) := by
  exact hf.op_fst_snd (T (H := H) (K := K)).continuous₂
    ⟨1, fun x y => by simp [T_norm]⟩ hg
lemma centered_integral {Z : Type*} [MeasurableSpace Z]
    [CompleteSpace H] [CompleteSpace K] (m : Measure Z) [IsProbabilityMeasure m]
    (f : Z → H) (g : Z → K) (a : H) (b : K)
    (hf : Integrable f m) (hg : Integrable g m)
    (hu : Integrable (fun z => T (f z) (g z)) m) :
    Integrable (fun z => T (f z-a) (g z-b)) m ∧
    (∫ z, T (f z-a) (g z-b) ∂m) =
      (∫ z, T (f z) (g z) ∂m) - T (∫ z, f z ∂m) b -
        T a (∫ z, g z ∂m) + T a b := by
  have hw := (T (H := H) (K := K)).flip b |>.integrable_comp hf
  have hv := (T (H := H) (K := K) a).integrable_comp hg
  have hc : Integrable (fun _ : Z => T a b) m := integrable_const _
  have he := ((hu.sub hw).sub hv).add hc
  have hF : Integrable (fun z => T (f z-a) (g z-b)) m := by
    apply he.congr
    exact Eventually.of_forall fun z => (T_sub_sub (f z) a (g z) b).symm
  refine ⟨hF, ?_⟩
  have h₁ := integral_sub hu hw
  have h₂ := integral_sub (hu.sub hw) hv
  have h₃ := integral_add ((hu.sub hw).sub hv) hc
  simp only [Pi.sub_apply, ContinuousLinearMap.flip_apply] at h₁ h₂ h₃
  have hwint := (T (H := H) (K := K)).flip b |>.integral_comp_comm hf
  simp only [ContinuousLinearMap.flip_apply] at hwint
  calc
    _ = ∫ z, (T (f z) (g z) - T (f z) b - T a (g z) + T a b) ∂m := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => T_sub_sub (f z) a (g z) b
    _ = _ := by
      rw [h₃,h₂,h₁, hwint,
        (T (H := H) (K := K) a).integral_comp_comm hg]
      simp

lemma inner_integral_square {Z E : Type*} [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (m : Measure Z) [SFinite m] (F : Z → E) (hF : Integrable F m) :
    (∫ p : Z × Z, inner ℝ (F p.1) (F p.2) ∂(m.prod m)) = ‖∫ z, F z ∂m‖^2 := by
  have h := integral_prod_bilin (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) hF hF
  change (∫ p : Z × Z, inner ℝ (F p.1) (F p.2) ∂(m.prod m)) =
    inner ℝ (∫ z, F z ∂m) (∫ z, F z ∂m) at h
  simpa only [real_inner_self_eq_norm_sq] using h

end Tensor

section Main
variable {X Y H K : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

lemma joint_memLp_fst (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ)
    (θ : Measure (X × Y)) [IsProbabilityMeasure θ]
    (h : FiniteFirstMoment (θ.map Prod.fst)) :
    MemLp (fun p : X × Y => ϕ p.1) 2 θ := by
  haveI : IsProbabilityMeasure (θ.map Prod.fst) := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  exact (memLp_map_measure_iff
    (embedding_continuous ϕ hϕ).stronglyMeasurable.aestronglyMeasurable
    measurable_fst.aemeasurable).mp (embedding_memLp ϕ hϕ (θ.map Prod.fst) h)

lemma joint_memLp_snd (ψ : Y → K) (hψ : IsNegTypeEmbedding ψ)
    (θ : Measure (X × Y)) [IsProbabilityMeasure θ]
    (h : FiniteFirstMoment (θ.map Prod.snd)) :
    MemLp (fun p : X × Y => ψ p.2) 2 θ := by
  haveI : IsProbabilityMeasure (θ.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact (memLp_map_measure_iff
    (embedding_continuous ψ hψ).stronglyMeasurable.aestronglyMeasurable
    measurable_snd.aemeasurable).mp (embedding_memLp ψ hψ (θ.map Prod.snd) h)

lemma dcov_centered_norm (ϕ : X → H) (ψ : Y → K)
    (hϕ : IsNegTypeEmbedding ϕ) (hψ : IsNegTypeEmbedding ψ)
    (θ : Measure (X × Y)) [IsProbabilityMeasure θ]
    (hμ : FiniteFirstMoment (θ.map Prod.fst))
    (hν : FiniteFirstMoment (θ.map Prod.snd))
    (hF : Integrable (fun p : X × Y =>
      T (ϕ p.1 - bary ϕ (θ.map Prod.fst)) (ψ p.2 - bary ψ (θ.map Prod.snd))) θ) :
    dcov θ = 4 * ‖∫ p : X × Y,
      T (ϕ p.1 - bary ϕ (θ.map Prod.fst)) (ψ p.2 - bary ψ (θ.map Prod.snd)) ∂θ‖^2 := by
  haveI : IsProbabilityMeasure (θ.map Prod.fst) := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure (θ.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hx := (proposition_3_5 ϕ hϕ (θ.map Prod.fst) hμ).2.2
  have hy := (proposition_3_5 ψ hψ (θ.map Prod.snd) hν).2.2
  unfold dcov
  calc
    _ = ∫ pq : (X × Y) × (X × Y), 4 * inner ℝ
        (T (ϕ pq.1.1 - bary ϕ (θ.map Prod.fst)) (ψ pq.1.2 - bary ψ (θ.map Prod.snd)))
        (T (ϕ pq.2.1 - bary ϕ (θ.map Prod.fst)) (ψ pq.2.2 - bary ψ (θ.map Prod.snd)))
        ∂(θ.prod θ) := by
      apply integral_congr_ae
      filter_upwards [] with pq
      rw [hx,hy,T_inner]
      ring
    _ = _ := by rw [integral_const_mul, inner_integral_square θ _ hF]

lemma tensor_bary_difference (ϕ : X → H) (ψ : Y → K)
    (hϕ : IsNegTypeEmbedding ϕ) (hψ : IsNegTypeEmbedding ψ)
    (θ : Measure (X × Y)) [IsProbabilityMeasure θ]
    (hμ : FiniteFirstMoment (θ.map Prod.fst))
    (hν : FiniteFirstMoment (θ.map Prod.snd)) :
    Integrable (tensorEmb ϕ ψ) θ ∧
    Integrable (fun p : X × Y =>
      T (ϕ p.1 - bary ϕ (θ.map Prod.fst)) (ψ p.2 - bary ψ (θ.map Prod.snd))) θ ∧
    (∫ p : X × Y,
      T (ϕ p.1 - bary ϕ (θ.map Prod.fst)) (ψ p.2 - bary ψ (θ.map Prod.snd)) ∂θ) =
      bary (tensorEmb ϕ ψ) θ - bary (tensorEmb ϕ ψ)
        ((θ.map Prod.fst).prod (θ.map Prod.snd)) := by
  haveI : IsProbabilityMeasure (θ.map Prod.fst) := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure (θ.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hf := embedding_integrable ϕ hϕ (θ.map Prod.fst) hμ
  have hg := embedding_integrable ψ hψ (θ.map Prod.snd) hν
  have hfθ : Integrable (fun p : X × Y => ϕ p.1) θ := hf.comp_aemeasurable measurable_fst.aemeasurable
  have hgθ : Integrable (fun p : X × Y => ψ p.2) θ := hg.comp_aemeasurable measurable_snd.aemeasurable
  have hu := tensor_integrable_L2 θ (joint_memLp_fst ϕ hϕ θ hμ) (joint_memLp_snd ψ hψ θ hν)
  have hc := centered_integral θ (fun p : X × Y => ϕ p.1) (fun p : X × Y => ψ p.2)
    (bary ϕ (θ.map Prod.fst)) (bary ψ (θ.map Prod.snd)) hfθ hgθ hu
  have hfx : (∫ p : X × Y, ϕ p.1 ∂θ) = bary ϕ (θ.map Prod.fst) :=
    (integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable).symm
  have hgy : (∫ p : X × Y, ψ p.2 ∂θ) = bary ψ (θ.map Prod.snd) :=
    (integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable).symm
  have hp : bary (tensorEmb ϕ ψ) ((θ.map Prod.fst).prod (θ.map Prod.snd)) =
      T (bary ϕ (θ.map Prod.fst)) (bary ψ (θ.map Prod.snd)) := by
    exact integral_prod_bilin (T (H := H) (K := K)) hf hg
  refine ⟨hu, hc.1, ?_⟩
  rw [hp]
  change (∫ p : X × Y, T (ϕ p.1 - bary ϕ (θ.map Prod.fst))
    (ψ p.2 - bary ψ (θ.map Prod.snd)) ∂θ) =
    (∫ p : X × Y, T (ϕ p.1) (ψ p.2) ∂θ) -
      T (bary ϕ (θ.map Prod.fst)) (bary ψ (θ.map Prod.snd))
  rw [hc.2,hfx,hgy]
  abel

end Main
end DistCovTensor


theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [SecondCountableTopology Y] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K]
    (ϕ : X → H) (ψ : Y → K) (hϕ : IsNegTypeEmbedding ϕ) (hψ : IsNegTypeEmbedding ψ)
    (θ : Measure (X × Y)) [IsProbabilityMeasure θ]
    (hμ : FiniteFirstMoment (θ.map Prod.fst)) (hν : FiniteFirstMoment (θ.map Prod.snd)) :
    Integrable (tensorEmb ϕ ψ) θ ∧
    dcov θ = 4 * ‖bary (tensorEmb ϕ ψ) θ
      - bary (tensorEmb ϕ ψ) ((θ.map Prod.fst).prod (θ.map Prod.snd))‖^2 := by
  obtain ⟨hu,hF,he⟩ := DistCovTensor.tensor_bary_difference ϕ ψ hϕ hψ θ hμ hν
  refine ⟨hu, ?_⟩
  rw [DistCovTensor.dcov_centered_norm ϕ ψ hϕ hψ θ hμ hν hF, he]

#print axioms solution
