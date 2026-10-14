-- Prove2me | solution 1 for DistCov.Indep.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T23:45:12.518418+00:00
-- url     : https://prove2.me/submissions/e8ed1626-fdee-4129-9ce6-0a5e4c0b6328

import Theorems.Thm_DistCov_Indep_proposition_3_1
import Theorems.Thm_DistCov_Indep_lemma_3_9

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
open DistCov.Indep
namespace DistCovM1Inject
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
end DistCovM1Inject

namespace DistCovTensorInject
open DistCovM1Inject
open scoped TensorProduct
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
end Tensor

section Measures
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def weighted (θ : Measure (X × Y)) (w : X → ℝ) : Measure Y :=
  (θ.withDensity (fun p => ENNReal.ofReal (w p.1))).map Prod.snd

lemma weighted_le (θ : Measure (X × Y)) (w : X → ℝ) (C : ℝ)
    (hw : ∀ x, w x ≤ C) : weighted θ w ≤ ENNReal.ofReal C • θ.map Prod.snd := by
  have hd : θ.withDensity (fun p => ENNReal.ofReal (w p.1)) ≤ ENNReal.ofReal C • θ := by
    rw [← withDensity_const]
    exact withDensity_mono (Eventually.of_forall fun p => ENNReal.ofReal_le_ofReal (hw p.1))
  simpa only [weighted, Measure.map_smul] using Measure.map_mono hd measurable_snd

lemma weighted_finite (θ : Measure (X × Y)) [IsFiniteMeasure θ]
    (w : X → ℝ) (C : ℝ) (hw : ∀ x, w x ≤ C) : IsFiniteMeasure (weighted θ w) := by
  letI := (θ.map Prod.snd).smul_finite (c := ENNReal.ofReal C) ENNReal.ofReal_ne_top
  exact isFiniteMeasure_of_le (ENNReal.ofReal C • θ.map Prod.snd) (weighted_le θ w C hw)

lemma weighted_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : Measure (X × Y)) (w : X → ℝ) (hw : Measurable w) (hn : ∀ x, 0 ≤ w x)
    (g : Y → V) (hg : StronglyMeasurable g) :
    (∫ y, g y ∂weighted θ w) = ∫ p : X × Y, w p.1 • g p.2 ∂θ := by
  unfold weighted
  rw [integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun p => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _)]
lemma weighted_mass (θ : Measure (X × Y)) (w : X → ℝ)
    (hw : Measurable w) (hn : ∀ x, 0 ≤ w x) (B : Set Y) (hB : MeasurableSet B) :
    (weighted θ w).real B = ∫ p : X × Y in Prod.snd ⁻¹' B, w p.1 ∂θ := by
  have h := weighted_integral θ w hw hn (B.indicator (fun _ : Y => (1 : ℝ)))
    (stronglyMeasurable_const.indicator hB)
  have hleft : (∫ y, B.indicator (fun _ : Y => (1 : ℝ)) y ∂weighted θ w) =
      (weighted θ w).real B := by rw [integral_indicator hB]; simp [hB]
  rw [hleft] at h
  rw [h]
  have he (p : X × Y) : w p.1 • B.indicator (fun _ : Y => (1 : ℝ)) p.2 =
      (Prod.snd ⁻¹' B).indicator (fun p : X × Y => w p.1) p := by
    by_cases hp : p.2 ∈ B <;> simp [Set.indicator, hp, smul_eq_mul]
  simp_rw [he]
  exact integral_indicator (measurable_snd hB)

def rectMarg (θ : Measure (X × Y)) (B : Set Y) : Measure X :=
  (θ.restrict (Prod.snd ⁻¹' B)).map Prod.fst

instance rectMarg_finite (θ : Measure (X × Y)) [IsFiniteMeasure θ] (B : Set Y) :
    IsFiniteMeasure (rectMarg θ B) := by unfold rectMarg; infer_instance

lemma rectMarg_le (θ : Measure (X × Y)) (B : Set Y) :
    rectMarg θ B ≤ θ.map Prod.fst := Measure.map_mono Measure.restrict_le_self measurable_fst

lemma rectMarg_prod (θ : Measure (X × Y)) (A : Set X) (B : Set Y)
    (hA : MeasurableSet A) (hB : MeasurableSet B) : rectMarg θ B A = θ (A ×ˢ B) := by
  unfold rectMarg
  rw [Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]
  congr 1
end Measures


section Metric
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y]

lemma firstMoment_le (μ ν : Measure Y) (h : FiniteFirstMoment ν) (hμν : μ ≤ ν) :
    FiniteFirstMoment μ := by
  obtain ⟨o,ho⟩ := h
  exact ⟨o, ho.mono_measure hμν⟩

lemma weighted_moment (θ : Measure (X × Y)) [IsFiniteMeasure θ]
    (w : X → ℝ) (C : ℝ) (hw : ∀ x, w x ≤ C)
    (h : FiniteFirstMoment (θ.map Prod.snd)) : FiniteFirstMoment (weighted θ w) := by
  obtain ⟨o,ho⟩ := h
  refine ⟨o, ?_⟩
  exact (ho.smul_measure (ENNReal.ofReal_ne_top)).mono_measure (weighted_le θ w C hw)

lemma shifted_inner (u v : E) :
    inner ℝ (augmented (id : E → E) u) (augmented id v) = inner ℝ u v + 1 := by
  simp only [augmented, inner_add_left, inner_add_right, shift.inner_map_map]
  have h₁ (x : E) : inner ℝ e0 (shift x) = 0 := by
    rw [e0, lp.inner_single_left]
    change inner ℝ (1 : ℝ) (eval0 (shift x)) = 0
    rw [shift_zero]; simp
  have h₂ (x : E) : inner ℝ (shift x) e0 = 0 := by rw [real_inner_comm]; exact h₁ x
  simp only [h₁, h₂, id_eq, zero_add, add_zero]
  simp [e0]

lemma anchored_bounds (ϕ : X → E) (hϕ : IsNegTypeEmbedding ϕ) (o z x : X) :
    0 ≤ inner ℝ (augmented (fun x => ϕ x - ϕ o) z)
      (augmented (fun x => ϕ x - ϕ o) x) ∧
    inner ℝ (augmented (fun x => ϕ x - ϕ o) z)
      (augmented (fun x => ϕ x - ϕ o) x) ≤ 1 + dist o z := by
  have he := norm_sub_sq_real (ϕ z - ϕ o) (ϕ x - ϕ o)
  have hd : (ϕ z - ϕ o) - (ϕ x - ϕ o) = ϕ z - ϕ x := by abel
  rw [hd, ← hϕ z x, ← hϕ z o, ← hϕ x o] at he
  have hs : inner ℝ (augmented (fun x => ϕ x - ϕ o) z)
      (augmented (fun x => ϕ x - ϕ o) x) = inner ℝ (ϕ z - ϕ o) (ϕ x - ϕ o) + 1 := shifted_inner _ _
  rw [hs]
  constructor
  · nlinarith [dist_triangle z o x, dist_comm x o]
  · nlinarith [dist_triangle x z o, dist_comm x z, dist_comm o z]
lemma embedding_memLp (ϕ : X → E) (hϕ : IsNegTypeEmbedding ϕ)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : FiniteFirstMoment μ) : MemLp ϕ 2 μ :=
  (memLp_two_iff_integrable_sq_norm
    (embedding_continuous ϕ hϕ).stronglyMeasurable.aestronglyMeasurable).mpr
    (norm_sq_integrable ϕ hϕ μ hμ)

lemma tensor_integrable (ϕ : X → E) (ψ : Y → E)
    (hϕ : IsNegTypeEmbedding ϕ) (hψ : IsNegTypeEmbedding ψ)
    (θ : Measure (X × Y)) [IsFiniteMeasure θ]
    (hμ : FiniteFirstMoment (θ.map Prod.fst))
    (hν : FiniteFirstMoment (θ.map Prod.snd)) : Integrable (tensorEmb ϕ ψ) θ := by
  have hf : MemLp (fun p : X × Y => ϕ p.1) 2 θ :=
    (memLp_map_measure_iff (embedding_continuous ϕ hϕ).stronglyMeasurable.aestronglyMeasurable
      measurable_fst.aemeasurable).mp (embedding_memLp ϕ hϕ (θ.map Prod.fst) hμ)
  have hg : MemLp (fun p : X × Y => ψ p.2) 2 θ :=
    (memLp_map_measure_iff (embedding_continuous ψ hψ).stronglyMeasurable.aestronglyMeasurable
      measurable_snd.aemeasurable).mp (embedding_memLp ψ hψ (θ.map Prod.snd) hν)
  exact tensor_integrable_L2 θ hf hg

lemma bounded_smul_integrable {Z : Type*} [MeasurableSpace Z] (m : Measure Z)
    (w : Z → ℝ) (g : Z → E) (hw : Measurable w) (hn : ∀ z, 0 ≤ w z)
    (C : ℝ) (hC : ∀ z, w z ≤ C) (hg : Integrable g m) :
    Integrable (fun z => w z • g z) m := by
  apply (hg.norm.const_mul C).mono' (hw.aestronglyMeasurable.smul hg.1)
  filter_upwards [] with z
  change ‖w z • g z‖ ≤ C * ‖g z‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hn z)]
  exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _)

lemma weighted_bary_eq (ϕ : X → E) (ψ : Y → E)
    (hϕ : IsNegTypeEmbedding ϕ) (hψ : IsNegTypeEmbedding ψ)
    (z : X) (C : ℝ)
    (hn : ∀ x, 0 ≤ inner ℝ (ϕ z) (ϕ x))
    (hC : ∀ x, inner ℝ (ϕ z) (ϕ x) ≤ C)
    (θ₁ θ₂ : Measure (X × Y)) [IsFiniteMeasure θ₁] [IsFiniteMeasure θ₂]
    (hm₁ : FiniteFirstMoment (θ₁.map Prod.fst)) (hm₂ : FiniteFirstMoment (θ₂.map Prod.fst))
    (hn₁ : FiniteFirstMoment (θ₁.map Prod.snd)) (hn₂ : FiniteFirstMoment (θ₂.map Prod.snd))
    (hb : bary (tensorEmb ϕ ψ) θ₁ = bary (tensorEmb ϕ ψ) θ₂) :
    bary ψ (weighted θ₁ (fun x => inner ℝ (ϕ z) (ϕ x))) =
      bary ψ (weighted θ₂ (fun x => inner ℝ (ϕ z) (ϕ x))) := by
  let w : X → ℝ := fun x => inner ℝ (ϕ z) (ϕ x)
  have hw : Measurable w := ((continuous_const.inner (embedding_continuous ϕ hϕ)).measurable)
  have hk (θ : Measure (X × Y)) [IsFiniteMeasure θ]
      (hμ : FiniteFirstMoment (θ.map Prod.fst)) (hν : FiniteFirstMoment (θ.map Prod.snd)) (k : E) :
      inner ℝ k (bary ψ (weighted θ w)) = inner ℝ (T (ϕ z) k) (bary (tensorEmb ϕ ψ) θ) := by
    have hg : Integrable (fun p : X × Y => ψ p.2) θ :=
      (embedding_integrable ψ hψ (θ.map Prod.snd) hν).comp_aemeasurable measurable_snd.aemeasurable
    have hv := bounded_smul_integrable θ (fun p : X × Y => w p.1) (fun p => ψ p.2)
      (hw.comp measurable_fst) (fun p => hn p.1) C (fun p => hC p.1) hg
    unfold bary
    rw [weighted_integral θ w hw hn ψ (embedding_continuous ψ hψ).stronglyMeasurable,
      ← integral_inner hv, ← integral_inner (tensor_integrable ϕ ψ hϕ hψ θ hμ hν)]
    apply integral_congr_ae
    filter_upwards [] with p
    change inner ℝ k (w p.1 • ψ p.2) = inner ℝ (T (ϕ z) k) (T (ϕ p.1) (ψ p.2))
    rw [inner_smul_right, T_inner]
  apply ext_inner_left ℝ
  intro k
  rw [hk θ₁ hm₁ hn₁ k, hk θ₂ hm₂ hn₂ k, hb]

lemma bary_eq_of_inner_image (ϕ : X → E) (μ ν : Measure X)
    (hμ : Integrable ϕ μ) (hν : Integrable ϕ ν)
    (h : ∀ x, inner ℝ (ϕ x) (bary ϕ μ) = inner ℝ (ϕ x) (bary ϕ ν)) :
    bary ϕ μ = bary ϕ ν := by
  let d := bary ϕ μ - bary ϕ ν
  have hz (x : X) : inner ℝ d (ϕ x) = 0 := by
    dsimp [d]
    rw [inner_sub_left]
    linarith [h x, real_inner_comm (bary ϕ μ) (ϕ x), real_inner_comm (bary ϕ ν) (ϕ x)]
  have hm : inner ℝ d (bary ϕ μ) = 0 := by
    unfold bary
    rw [← integral_inner hμ]
    simp_rw [hz]; simp
  have hn : inner ℝ d (bary ϕ ν) = 0 := by
    unfold bary
    rw [← integral_inner hν]
    simp_rw [hz]; simp
  have hd : inner ℝ d d = 0 := by dsimp [d]; rw [inner_sub_right, hm, hn]; ring
  exact sub_eq_zero.mp ((inner_self_eq_zero).mp hd)

lemma rectMarg_inner (ϕ : X → E) (hϕ : IsNegTypeEmbedding ϕ)
    (θ : Measure (X × Y)) [IsFiniteMeasure θ]
    (hm : FiniteFirstMoment (θ.map Prod.fst)) (B : Set Y) (z : X) :
    inner ℝ (ϕ z) (bary ϕ (rectMarg θ B)) =
      ∫ p : X × Y in Prod.snd ⁻¹' B, inner ℝ (ϕ z) (ϕ p.1) ∂θ := by
  have h := firstMoment_le (rectMarg θ B) (θ.map Prod.fst) hm (rectMarg_le θ B)
  have hi := embedding_integrable ϕ hϕ (rectMarg θ B) h
  unfold bary
  rw [← integral_inner hi]
  exact integral_map measurable_fst.aemeasurable
    (continuous_const.inner (embedding_continuous ϕ hϕ)).stronglyMeasurable.aestronglyMeasurable

lemma tensor_inj_of_bounded (ϕ : X → E) (ψ : Y → E)
    (hϕ : IsNegTypeEmbedding ϕ) (hψ : IsNegTypeEmbedding ψ)
    (hφinj : BaryInjM1 ϕ) (hψinj : BaryInjM1 ψ)
    (hbound : ∀ z, ∃ C : ℝ, ∀ x, 0 ≤ inner ℝ (ϕ z) (ϕ x) ∧ inner ℝ (ϕ z) (ϕ x) ≤ C) :
    TensorBaryInjM11 ϕ ψ := by
  intro θ₁ θ₂ hf₁ hf₂ hm₁ hn₁ hm₂ hn₂ hb
  letI := hf₁
  letI := hf₂
  apply Measure.ext_prod
  intro A B hA hB
  have hrect : rectMarg θ₁ B = rectMarg θ₂ B := by
    have hr₁ := firstMoment_le (rectMarg θ₁ B) (θ₁.map Prod.fst) hm₁ (rectMarg_le θ₁ B)
    have hr₂ := firstMoment_le (rectMarg θ₂ B) (θ₂.map Prod.fst) hm₂ (rectMarg_le θ₂ B)
    apply hφinj _ _ inferInstance inferInstance hr₁ hr₂
    apply bary_eq_of_inner_image ϕ _ _
      (embedding_integrable ϕ hϕ _ hr₁) (embedding_integrable ϕ hϕ _ hr₂)
    intro z
    obtain ⟨C,hC⟩ := hbound z
    let w : X → ℝ := fun x => inner ℝ (ϕ z) (ϕ x)
    have hw : Measurable w := (continuous_const.inner (embedding_continuous ϕ hϕ)).measurable
    have hfν₁ := weighted_finite θ₁ w C (fun x => (hC x).2)
    have hfν₂ := weighted_finite θ₂ w C (fun x => (hC x).2)
    have hν₁ := weighted_moment θ₁ w C (fun x => (hC x).2) hn₁
    have hν₂ := weighted_moment θ₂ w C (fun x => (hC x).2) hn₂
    have he : weighted θ₁ w = weighted θ₂ w := hψinj _ _ hfν₁ hfν₂ hν₁ hν₂
      (weighted_bary_eq ϕ ψ hϕ hψ z C (fun x => (hC x).1) (fun x => (hC x).2)
        θ₁ θ₂ hm₁ hm₂ hn₁ hn₂ hb)
    rw [rectMarg_inner ϕ hϕ θ₁ hm₁ B z, rectMarg_inner ϕ hϕ θ₂ hm₂ B z,
      ← weighted_mass θ₁ w hw (fun x => (hC x).1) B hB,
      ← weighted_mass θ₂ w hw (fun x => (hC x).1) B hB, he]
  rw [← rectMarg_prod θ₁ A B hA hB, ← rectMarg_prod θ₂ A B hA hB, hrect]

end Metric
end DistCovTensorInject


theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [SecondCountableTopology Y]
    (hX : StrongNegType X) (hY : StrongNegType Y) :
    ∃ ϕ : X → L2N, ∃ ψ : Y → L2N, IsNegTypeEmbedding ϕ ∧ IsNegTypeEmbedding ψ ∧
      BaryInjProb ϕ ∧ BaryInjProb ψ ∧ TensorBaryInjM11 ϕ ψ := by
  classical
  obtain ⟨ϕ,hϕ,hiϕ⟩ := lemma_3_9 hX
  obtain ⟨ψ,hψ,hiψ⟩ := lemma_3_9 hY
  have hpψ := (proposition_3_1 ψ hψ).mp hY
  by_cases hx : Nonempty X
  · obtain ⟨o⟩ := hx
    let χ : X → L2N := fun x => ϕ x - ϕ o
    have hχ : IsNegTypeEmbedding χ := by
      intro x y
      have he : χ x - χ y = ϕ x - ϕ y := by dsimp [χ]; abel
      rw [he]
      exact hϕ x y
    have hiχ := (proposition_3_1 χ hχ).mp hX
    let Φ := DistCovM1Inject.augmented χ
    have hΦ := DistCovM1Inject.augmented_embedding χ hχ
    have hiΦ := DistCovM1Inject.augmented_inj χ hχ hiχ
    have hpΦ := (proposition_3_1 Φ hΦ).mp hX
    refine ⟨Φ,ψ,hΦ,hψ,hpΦ,hpψ, ?_⟩
    apply DistCovTensorInject.tensor_inj_of_bounded Φ ψ hΦ hψ hiΦ hiψ
    intro z
    exact ⟨1 + dist o z, fun x => DistCovTensorInject.anchored_bounds ϕ hϕ o z x⟩
  · letI : IsEmpty X := not_nonempty_iff.mp hx
    refine ⟨ϕ,ψ,hϕ,hψ,(proposition_3_1 ϕ hϕ).mp hX,hpψ, ?_⟩
    intro θ₁ θ₂ hf₁ hf₂ hm₁
    obtain ⟨o,ho⟩ := hm₁
    exact isEmptyElim o

#print axioms solution
