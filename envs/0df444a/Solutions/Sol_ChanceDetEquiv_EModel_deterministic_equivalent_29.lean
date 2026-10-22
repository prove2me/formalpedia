-- Prove2me | solution 1 for ChanceDetEquiv.EModel.deterministic_equivalent_29
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T18:05:47.35483+00:00
-- url     : https://prove2.me/submissions/3eef0b2f-d8e4-45b6-8c7a-3241f4eb9700

import Mathlib
import Definitions.Def_ChanceDetEquiv_EModel_Model

set_option autoImplicit false

namespace ChanceDetEquiv.EModel.AuxF1d

open MeasureTheory ProbabilityTheory Matrix ChanceDetEquiv.EModel

/-! ### Phi facts (copied from our accepted Cohen2019 siblings) -/

theorem phi_strictMono : StrictMono Cohen2019.Robust.Phi := by
  intro a b hab
  unfold Cohen2019.Robust.Phi
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have hpos : (gaussianReal 0 1) (Set.Ioc a b) ≠ 0 := by
    intro h
    have h2 := gaussianReal_absolutelyContinuous' (0 : ℝ) hv h
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at h2
    linarith
  have hm := (cdf (gaussianReal 0 1)).measure_Ioc a b
  rw [measure_cdf] at hm
  rw [hm] at hpos
  have : ¬ (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a ≤ 0) := by
    intro hle; exact hpos (ENNReal.ofReal_eq_zero.mpr hle)
  linarith

theorem phi_continuous : Continuous Cohen2019.Robust.Phi := by
  have hfun : Cohen2019.Robust.Phi = fun t => cdf (gaussianReal 0 1) t := rfl
  rw [hfun, continuous_iff_continuousAt]
  intro a
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [(monotone_cdf (gaussianReal 0 1)).continuousAt_iff_leftLim_eq_rightLim,
    StieltjesFunction.rightLim_eq]
  have hs := (cdf (gaussianReal 0 1)).measure_singleton a
  rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at hs
  have hle := (monotone_cdf (gaussianReal 0 1)).leftLim_le (le_refl a)
  linarith

open Filter in
theorem phi_inv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal q) = q := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually
    (Iio_mem_nhds hq0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually
    (Ioi_mem_nhds hq1)).exists
  have hmem : q ∈ Set.Icc (Cohen2019.Robust.Phi a) (Cohen2019.Robust.Phi b) :=
    ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ a b phi_continuous hmem
  have hS : {s : ℝ | q ≤ Cohen2019.Robust.Phi s} = Set.Ici t := by
    ext s
    simp only [Set.mem_Ici]
    rw [← ht]
    exact phi_strictMono.le_iff_le
  unfold Cohen2019.Robust.PhiInvReal
  rw [hS, csInf_Ici, ht]

theorem phi_def (t : ℝ) :
    (gaussianReal 0 1).real (Set.Iic t) = Cohen2019.Robust.Phi t := by
  rw [Cohen2019.Robust.Phi, cdf_eq_real]

theorem phi_neg (t : ℝ) : Cohen2019.Robust.Phi (-t) = 1 - Cohen2019.Robust.Phi t := by
  have h := gaussianReal_map_neg (μ := (0:ℝ)) (v := 1)
  rw [neg_zero] at h
  rw [← phi_def, ← phi_def]
  have h1 : (gaussianReal 0 1).real (Set.Iic (-t)) = (gaussianReal 0 1).real (Set.Ici t) := by
    conv_lhs => rw [← h]
    rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext y
    simp
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [h1, ← Set.compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio,
    measureReal_congr Iio_ae_eq_Iic]

lemma phi_zero : Cohen2019.Robust.Phi 0 = 1 / 2 := by
  have := phi_neg 0
  rw [neg_zero] at this
  linarith

lemma K_pos {α : ℝ} (h1 : 1 / 2 < α) (h2 : α < 1) : 0 < K α := by
  have hK := phi_inv (q := α) (by linarith) h2
  by_contra hle
  push_neg at hle
  have := phi_strictMono.monotone hle
  have hK' : Cohen2019.Robust.Phi (K α) = α := hK
  rw [hK', phi_zero] at this
  linarith

lemma le_Phi_iff {α t : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    α ≤ Cohen2019.Robust.Phi t ↔ K α ≤ t := by
  conv_lhs => rw [← phi_inv h0 h1]
  exact phi_strictMono.le_iff_le

/-! ### Gaussian facts -/

lemma gauss_Iic_zero (μg : ℝ) (s : NNReal) (hs : 0 < (s : ℝ)) :
    (gaussianReal μg s).real (Set.Iic 0) = Cohen2019.Robust.Phi (-μg / Real.sqrt s) := by
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hmap : (gaussianReal 0 1).map (fun x => Real.sqrt s * x + μg) = gaussianReal μg s := by
    have h1 := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt s)
    have hc : (fun x => Real.sqrt s * x + μg) = (fun x => x + μg) ∘ (fun x => Real.sqrt s * x) :=
      rfl
    rw [hc, ← Measure.map_map (by fun_prop) (by fun_prop), h1, gaussianReal_map_add_const]
    congr 1
    · ring
    · ext
      simp [Real.sq_sqrt hs.le]
  rw [← hmap, map_measureReal_apply (by fun_prop) measurableSet_Iic]
  have hpre : (fun x => Real.sqrt s * x + μg) ⁻¹' Set.Iic 0 = Set.Iic (-μg / Real.sqrt s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic]
    rw [le_div_iff₀ hr]
    constructor <;> intro h <;> linarith
  rw [hpre, phi_def]

lemma gauss_moments {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (Y : Ω → ℝ) (μg : ℝ)
    (s : NNReal) (h : P.map Y = gaussianReal μg s) :
    AEMeasurable Y P ∧ MemLp Y 2 P ∧ ∫ ω, Y ω ∂P = μg ∧ ∫ ω, Y ω ^ 2 ∂P = μg ^ 2 + s := by
  have hY : AEMeasurable Y P := by
    by_contra hY
    rw [Measure.map_of_not_aemeasurable hY] at h
    have := congrArg (fun ν : Measure ℝ => ν Set.univ) h
    simp at this
  refine ⟨hY, ?_, ?_, ?_⟩
  · have hm : MemLp id 2 (P.map Y) := by
      rw [h]; exact memLp_id_gaussianReal' 2 (by norm_num)
    exact (memLp_map_measure_iff aestronglyMeasurable_id hY).1 hm
  · have hm := integral_map (f := id) hY aestronglyMeasurable_id
    simp only [id] at hm
    rw [← hm, h]
    exact integral_id_gaussianReal
  · rw [← integral_map (f := fun x : ℝ => x ^ 2) hY (by fun_prop), h]
    have hv := variance_eq_sub (memLp_id_gaussianReal' (μ := μg) (v := s) 2 (by norm_num))
    rw [variance_id_gaussianReal] at hv
    have he : ∫ x, id x ∂(gaussianReal μg s) = μg := integral_id_gaussianReal
    have he2 : ∫ x, (id ^ 2 : ℝ → ℝ) x ∂(gaussianReal μg s) = ∫ x, x ^ 2 ∂(gaussianReal μg s) :=
      rfl
    rw [he, he2] at hv
    linarith

/-- Row equivalence in Gaussian terms. -/
lemma row_iff (μg : ℝ) (s : NNReal) (α : ℝ) (h1 : 1 / 2 < α) (h2 : α < 1) :
    α ≤ (gaussianReal μg s).real (Set.Iic 0) ↔
      ∃ v : ℝ, 0 ≤ -μg - v ∧ 0 ≤ -(K α) ^ 2 * (μg ^ 2 + s) + (K α) ^ 2 * (-μg) ^ 2 + v ^ 2 ∧
        0 ≤ v := by
  have hK := K_pos h1 h2
  by_cases hs : (s : ℝ) = 0
  · have hs0 : s = 0 := by exact_mod_cast hs
    subst hs0
    rw [gaussianReal_zero_var]
    by_cases hμ : μg ≤ 0
    · have hr : (Measure.dirac μg).real (Set.Iic 0) = 1 := by
        simp [measureReal_def, Measure.dirac_apply' _ measurableSet_Iic, hμ]
      rw [hr]
      constructor
      · intro _
        exact ⟨0, by linarith, by simp, le_refl _⟩
      · intro _; linarith
    · have hr : (Measure.dirac μg).real (Set.Iic 0) = 0 := by
        simp [measureReal_def, Measure.dirac_apply' _ measurableSet_Iic, hμ]
      rw [hr]
      constructor
      · intro h; linarith
      · rintro ⟨v, hv1, _, hv3⟩; exact absurd (by linarith : μg ≤ 0) hμ
  · have hs' : 0 < (s : ℝ) := lt_of_le_of_ne s.2 (Ne.symm hs)
    have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs'
    have hrr : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs'.le
    rw [gauss_Iic_zero μg s hs', le_Phi_iff (by linarith) h2, le_div_iff₀ hr]
    constructor
    · intro h
      refine ⟨K α * Real.sqrt s, by linarith, ?_, by positivity⟩
      have : (K α * Real.sqrt s) ^ 2 = (K α) ^ 2 * s := by rw [mul_pow, hrr]
      nlinarith
    · rintro ⟨v, hv1, hv2, hv3⟩
      have hsq : (K α * Real.sqrt s) ^ 2 ≤ v ^ 2 := by
        rw [mul_pow, hrr]; nlinarith
      have hKr : 0 ≤ K α * Real.sqrt s := by positivity
      have : K α * Real.sqrt s ≤ v := by nlinarith
      linarith

/-! ### Linear algebra of the residual -/

lemma AD_expand {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (x : Fin m → ℝ) (i : Fin m) :
    (A *ᵥ (D *ᵥ x)) i = ∑ j : Fin n, ∑ k : Fin m, (A i j * D j k) * x k := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

section res
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {m n : ℕ}

lemma res_memLp (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ)
    (hb : ∀ k, MemLp (fun ω => b ω k) 2 P) (D : Matrix (Fin n) (Fin m) ℝ) (i : Fin m) :
    MemLp (fun ω => (A *ᵥ (D *ᵥ b ω)) i - b ω i) 2 P := by
  have he : (fun ω => (A *ᵥ (D *ᵥ b ω)) i - b ω i) =
      fun ω => (∑ j : Fin n, ∑ k : Fin m, (A i j * D j k) * b ω k) - b ω i := by
    funext ω; rw [AD_expand]
  rw [he]
  exact (memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun k _ => (hb k).const_mul _).sub (hb i)

lemma res_integral (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ)
    (hb : ∀ k, MemLp (fun ω => b ω k) 2 P) (D : Matrix (Fin n) (Fin m) ℝ) (i : Fin m) :
    ∫ ω, ((A *ᵥ (D *ᵥ b ω)) i - b ω i) ∂P = - muRow P A b D i := by
  have hbi : ∀ k, Integrable (fun ω => b ω k) P := fun k => (hb k).integrable (by norm_num)
  have he : (fun ω => (A *ᵥ (D *ᵥ b ω)) i - b ω i) =
      fun ω => (∑ j : Fin n, ∑ k : Fin m, (A i j * D j k) * b ω k) - b ω i := by
    funext ω; rw [AD_expand]
  rw [he, integral_sub (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (hbi k).const_mul _) (hbi i),
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => (hbi k).const_mul _]
  have : ∀ j : Fin n, ∫ ω, ∑ k : Fin m, (A i j * D j k) * b ω k ∂P
      = ∑ k : Fin m, (A i j * D j k) * meanVec P b k := by
    intro j
    rw [integral_finsetSum _ fun k _ => (hbi k).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]; rfl
  simp only [this, muRow, AD_expand]
  simp only [meanVec]
  ring

lemma res_comb (A : Matrix (Fin m) (Fin n) ℝ) (D1 D2 : Matrix (Fin n) (Fin m) ℝ)
    (x : Fin m → ℝ) (i : Fin m) (a c : ℝ) (hac : a + c = 1) :
    (A *ᵥ ((a • D1 + c • D2) *ᵥ x)) i - x i =
      a * ((A *ᵥ (D1 *ᵥ x)) i - x i) + c * ((A *ᵥ (D2 *ᵥ x)) i - x i) := by
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (x i) * hac

/-- Jensen for the square on a probability space. -/
lemma sq_integral_le (Z : Ω → ℝ) (hZ : MemLp Z 2 P) : (∫ ω, Z ω ∂P) ^ 2 ≤ ∫ ω, Z ω ^ 2 ∂P := by
  set mm := ∫ ω, Z ω ∂P with hm
  have hZi : Integrable Z P := hZ.integrable (by norm_num)
  have h0 : 0 ≤ ∫ ω, (Z ω - mm) ^ 2 ∂P := integral_nonneg (fun _ => sq_nonneg _)
  have hexp : (fun ω => (Z ω - mm) ^ 2) = fun ω => (Z ω ^ 2 - (2 * mm) * Z ω) + mm ^ 2 := by
    funext ω; ring
  have i1 : Integrable (fun ω => Z ω ^ 2 - (2 * mm) * Z ω) P :=
    hZ.integrable_sq.sub (hZi.const_mul _)
  have i2 : Integrable (fun ω => Z ω ^ 2) P := hZ.integrable_sq
  have i3 : Integrable (fun ω => (2 * mm) * Z ω) P := hZi.const_mul _
  rw [hexp, integral_add i1 (integrable_const _), integral_sub i2 i3, integral_const_mul,
    integral_const] at h0
  simp only [probReal_univ, one_smul] at h0
  rw [← hm] at h0
  nlinarith

lemma integral_comb_sq (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (r s : ℝ) :
    ∫ ω, (r * X ω + s * Y ω) ^ 2 ∂P =
      r ^ 2 * ∫ ω, X ω ^ 2 ∂P + 2 * r * s * ∫ ω, X ω * Y ω ∂P + s ^ 2 * ∫ ω, Y ω ^ 2 ∂P := by
  have hXY : Integrable (fun ω => X ω * Y ω) P := by
    have := hX.integrable_mul hY (p := 2) (q := 2)
    simpa [Pi.mul_def] using this
  have hexp : (fun ω => (r * X ω + s * Y ω) ^ 2) =
      fun ω => (r ^ 2 * X ω ^ 2 + (2 * r * s) * (X ω * Y ω)) + s ^ 2 * Y ω ^ 2 := by
    funext ω; ring
  have i1 : Integrable (fun ω => r ^ 2 * X ω ^ 2) P := hX.integrable_sq.const_mul _
  have i2 : Integrable (fun ω => (2 * r * s) * (X ω * Y ω)) P := hXY.const_mul _
  have i3 : Integrable (fun ω => s ^ 2 * Y ω ^ 2) P := hY.integrable_sq.const_mul _
  have i12 : Integrable (fun ω => r ^ 2 * X ω ^ 2 + (2 * r * s) * (X ω * Y ω)) P := i1.add i2
  rw [hexp, integral_add i12 i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul]

lemma integral_comb (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (r s : ℝ) :
    ∫ ω, (r * X ω + s * Y ω) ∂P = r * ∫ ω, X ω ∂P + s * ∫ ω, Y ω ∂P := by
  rw [integral_add ((hX.integrable (by norm_num)).const_mul _)
      ((hY.integrable (by norm_num)).const_mul _), integral_const_mul, integral_const_mul]

/-- Convexity of the variance cone constraint. -/
lemma quad_comb (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (K2 a1 a2 l1 l2 : ℝ) (hK : 0 ≤ K2)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2)
    (h1 : K2 * (∫ ω, X ω ^ 2 ∂P - (∫ ω, X ω ∂P) ^ 2) ≤ a1 ^ 2)
    (h2 : K2 * (∫ ω, Y ω ^ 2 ∂P - (∫ ω, Y ω ∂P) ^ 2) ≤ a2 ^ 2) :
    K2 * (∫ ω, (l1 * X ω + l2 * Y ω) ^ 2 ∂P - (∫ ω, (l1 * X ω + l2 * Y ω) ∂P) ^ 2)
      ≤ (l1 * a1 + l2 * a2) ^ 2 := by
  set A := ∫ ω, X ω ^ 2 ∂P
  set B := ∫ ω, X ω * Y ω ∂P
  set C := ∫ ω, Y ω ^ 2 ∂P
  set mX := ∫ ω, X ω ∂P
  set mY := ∫ ω, Y ω ∂P
  have hq : ∀ r s : ℝ, 0 ≤ (r ^ 2 * A + 2 * r * s * B + s ^ 2 * C) - (r * mX + s * mY) ^ 2 := by
    intro r s
    have hZ : MemLp (fun ω => r * X ω + s * Y ω) 2 P := (hX.const_mul r).add (hY.const_mul s)
    have j := sq_integral_le _ hZ
    rw [integral_comb_sq X Y hX hY, integral_comb X Y hX hY] at j
    linarith
  set V1 := A - mX ^ 2
  set V2 := C - mY ^ 2
  set Cv := B - mX * mY
  have hV1 : 0 ≤ V1 := by have := hq 1 0; simp only [V1]; nlinarith
  have hV2 : 0 ≤ V2 := by have := hq 0 1; simp only [V2]; nlinarith
  have hdisc : discrim V2 (2 * Cv) V1 ≤ 0 := by
    apply discrim_le_zero
    intro x
    have := hq 1 x
    simp only [V1, V2, Cv]; nlinarith
  rw [discrim] at hdisc
  have hCv : (K2 * Cv) ^ 2 ≤ (K2 * V1) * (K2 * V2) := by
    have : Cv ^ 2 ≤ V1 * V2 := by nlinarith
    have hK2 : 0 ≤ K2 ^ 2 := sq_nonneg _
    nlinarith
  have e1 : K2 * V1 ≤ a1 ^ 2 := h1
  have e2 : K2 * V2 ≤ a2 ^ 2 := h2
  have p2 : 0 ≤ K2 * V2 := mul_nonneg hK hV2
  have hprod : (K2 * Cv) ^ 2 ≤ (a1 * a2) ^ 2 := by
    calc (K2 * Cv) ^ 2 ≤ (K2 * V1) * (K2 * V2) := hCv
      _ ≤ a1 ^ 2 * a2 ^ 2 := mul_le_mul e1 e2 p2 (sq_nonneg _)
      _ = (a1 * a2) ^ 2 := by ring
  have hC' : K2 * Cv ≤ a1 * a2 := by
    exact (abs_le_of_sq_le_sq' hprod (mul_nonneg ha1 ha2)).2
  rw [integral_comb_sq X Y hX hY, integral_comb X Y hX hY]
  have key : K2 * ((l1 ^ 2 * A + 2 * l1 * l2 * B + l2 ^ 2 * C) - (l1 * mX + l2 * mY) ^ 2)
      = l1 ^ 2 * (K2 * V1) + 2 * l1 * l2 * (K2 * Cv) + l2 ^ 2 * (K2 * V2) := by
    simp only [V1, V2, Cv]; ring
  rw [key]
  have t1 : l1 ^ 2 * (K2 * V1) ≤ l1 ^ 2 * a1 ^ 2 := mul_le_mul_of_nonneg_left e1 (sq_nonneg _)
  have t2 : l2 ^ 2 * (K2 * V2) ≤ l2 ^ 2 * a2 ^ 2 := mul_le_mul_of_nonneg_left e2 (sq_nonneg _)
  have t3 : 2 * l1 * l2 * (K2 * Cv) ≤ 2 * l1 * l2 * (a1 * a2) :=
    mul_le_mul_of_nonneg_left hC' (by positivity)
  nlinarith

/-- Each row of (18) and (29) under normality. -/
lemma row_data (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ)
    (hb : ∀ k, MemLp (fun ω => b ω k) 2 P) (hnormal : RowsNormal P A b)
    (D : Matrix (Fin n) (Fin m) ℝ) (i : Fin m) :
    ∃ (μg : ℝ) (s : NNReal),
      P.real {ω | (A *ᵥ (D *ᵥ b ω)) i ≤ b ω i} = (gaussianReal μg s).real (Set.Iic 0) ∧
      muRow P A b D i = -μg ∧ sigmaSq P A b D i = μg ^ 2 + s := by
  obtain ⟨μg, s, h⟩ := hnormal D i
  obtain ⟨hY, _, hI, hI2⟩ := gauss_moments _ μg s h
  refine ⟨μg, s, ?_, ?_, ?_⟩
  · have hset : {ω | (A *ᵥ (D *ᵥ b ω)) i ≤ b ω i} =
        (fun ω => (A *ᵥ (D *ᵥ b ω)) i - b ω i) ⁻¹' Set.Iic 0 := by
      ext ω; simp [sub_nonpos]
    rw [hset, ← h, measureReal_def, measureReal_def,
      Measure.map_apply_of_aemeasurable hY measurableSet_Iic]
  · have := res_integral A b hb D i
    linarith
  · exact hI2

end res

end ChanceDetEquiv.EModel.AuxF1d

open MeasureTheory ProbabilityTheory Matrix ChanceDetEquiv.EModel in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Ω → Fin m → ℝ) (c : Ω → Fin n → ℝ) (α : Fin m → ℝ)
    (hb : ∀ k, MemLp (fun ω => b ω k) 2 P)
    (hc : ∀ j, Integrable (fun ω => c ω j) P)
    (hcb : ∀ j k, Integrable (fun ω => c ω j * b ω k) P)
    (huncorr : ∀ j k, ∫ ω, c ω j * b ω k ∂P = (∫ ω, c ω j ∂P) * (∫ ω, b ω k ∂P))
    (hnormal : RowsNormal P A b)
    (hα_lo : ∀ i, 1 / 2 < α i) (hα_hi : ∀ i, α i < 1) :
    (∀ D : Matrix (Fin n) (Fin m) ℝ, IsChanceFeasible18 P A b α D ↔ ∃ v, Sys29 P A b α D v) ∧
    (∀ D : Matrix (Fin n) (Fin m) ℝ, expectedObjective P b c D = detObjective P b c D) ∧
    Convex ℝ {p : Matrix (Fin n) (Fin m) ℝ × (Fin m → ℝ) | Sys29 P A b α p.1 p.2} := by
  refine ⟨?_, ?_, ?_⟩
  · intro D
    have key : ∀ i : Fin m, α i ≤ P.real {ω | (A *ᵥ (D *ᵥ b ω)) i ≤ b ω i} ↔
        ∃ w : ℝ, 0 ≤ muRow P A b D i - w ∧
          0 ≤ -(K (α i)) ^ 2 * sigmaSq P A b D i + (K (α i)) ^ 2 * (muRow P A b D i) ^ 2
            + w ^ 2 ∧ 0 ≤ w := by
      intro i
      obtain ⟨μg, s, hP, hmu, hsig⟩ := AuxF1d.row_data A b hb hnormal D i
      rw [hP, hmu, hsig]
      exact AuxF1d.row_iff μg s (α i) (hα_lo i) (hα_hi i)
    constructor
    · intro h
      choose v hv using fun i => (key i).1 (h i)
      exact ⟨v, hv⟩
    · rintro ⟨v, hv⟩ i
      exact (key i).2 ⟨v i, hv i⟩
  · intro D
    unfold expectedObjective detObjective
    have hexp : (fun ω => c ω ⬝ᵥ (D *ᵥ b ω)) =
        fun ω => ∑ j : Fin n, ∑ k : Fin m, D j k * (c ω j * b ω k) := by
      funext ω
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have hint : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        Integrable (fun ω => ∑ k : Fin m, D j k * (c ω j * b ω k)) P := fun j _ =>
      integrable_finsetSum _ fun k _ => (hcb j k).const_mul _
    rw [hexp, integral_finsetSum _ hint]
    have : ∀ j : Fin n, ∫ ω, ∑ k : Fin m, D j k * (c ω j * b ω k) ∂P
        = ∑ k : Fin m, D j k * (meanVec P c j * meanVec P b k) := by
      intro j
      have hint2 : ∀ k ∈ (Finset.univ : Finset (Fin m)),
          Integrable (fun ω => D j k * (c ω j * b ω k)) P := fun k _ => (hcb j k).const_mul _
      rw [integral_finsetSum _ hint2]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul, huncorr]; rfl
    simp only [this, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  · intro p hp q hq a c' ha hc' hac
    have hp' : Sys29 P A b α p.1 p.2 := hp
    have hq' : Sys29 P A b α q.1 q.2 := hq
    show Sys29 P A b α (a • p + c' • q).1 (a • p + c' • q).2
    intro i
    obtain ⟨hp1, hp2, hp3⟩ := hp' i
    obtain ⟨hq1, hq2, hq3⟩ := hq' i
    set Y1 : Ω → ℝ := fun ω => (A *ᵥ (p.1 *ᵥ b ω)) i - b ω i with hY1
    set Y2 : Ω → ℝ := fun ω => (A *ᵥ (q.1 *ᵥ b ω)) i - b ω i with hY2
    have hL1 : MemLp Y1 2 P := AuxF1d.res_memLp A b hb p.1 i
    have hL2 : MemLp Y2 2 P := AuxF1d.res_memLp A b hb q.1 i
    have hI1 : ∫ ω, Y1 ω ∂P = - muRow P A b p.1 i := AuxF1d.res_integral A b hb p.1 i
    have hI2 : ∫ ω, Y2 ω ∂P = - muRow P A b q.1 i := AuxF1d.res_integral A b hb q.1 i
    have hS1 : sigmaSq P A b p.1 i = ∫ ω, Y1 ω ^ 2 ∂P := rfl
    have hS2 : sigmaSq P A b q.1 i = ∫ ω, Y2 ω ^ 2 ∂P := rfl
    have hfst : (a • p + c' • q).1 = a • p.1 + c' • q.1 := rfl
    have hsnd : (a • p + c' • q).2 = a • p.2 + c' • q.2 := rfl
    have hYc : (fun ω => (A *ᵥ ((a • p + c' • q).1 *ᵥ b ω)) i - b ω i) =
        fun ω => a * Y1 ω + c' * Y2 ω := by
      funext ω
      rw [hfst, AuxF1d.res_comb A p.1 q.1 (b ω) i a c' hac]
    have hIc := AuxF1d.res_integral A b hb (a • p + c' • q).1 i
    rw [hYc, AuxF1d.integral_comb Y1 Y2 hL1 hL2] at hIc
    have hSc : sigmaSq P A b (a • p + c' • q).1 i = ∫ ω, (a * Y1 ω + c' * Y2 ω) ^ 2 ∂P := by
      unfold sigmaSq
      congr 1
      funext ω
      rw [hfst, AuxF1d.res_comb A p.1 q.1 (b ω) i a c' hac]
    have hmu : muRow P A b (a • p + c' • q).1 i =
        a * muRow P A b p.1 i + c' * muRow P A b q.1 i := by
      rw [hI1, hI2] at hIc; linarith
    have hQ := AuxF1d.quad_comb Y1 Y2 hL1 hL2 ((K (α i)) ^ 2) (p.2 i) (q.2 i) a c' (sq_nonneg _)
      hp3 hq3 ha hc'
      (by rw [hI1, ← hS1, neg_sq]; linarith) (by rw [hI2, ← hS2, neg_sq]; linarith)
    rw [AuxF1d.integral_comb Y1 Y2 hL1 hL2, hI1, hI2, ← hSc] at hQ
    have hv : (a • p + c' • q).2 i = a * p.2 i + c' * q.2 i := by
      rw [hsnd]; simp
    refine ⟨?_, ?_, ?_⟩
    · rw [hmu, hv]; nlinarith
    · rw [hmu, hv]
      have : a * -muRow P A b p.1 i + c' * -muRow P A b q.1 i =
          -(a * muRow P A b p.1 i + c' * muRow P A b q.1 i) := by ring
      rw [this, neg_sq] at hQ
      nlinarith
    · rw [hv]; positivity
