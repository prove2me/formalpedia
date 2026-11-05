-- Prove2me | solution 1 for DDROCS.theorem_10_cs_sets
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T10:06:55.65119+00:00
-- url     : https://prove2.me/submissions/bc3ddbfe-32a1-40a2-b3d8-322b3c753ce1

import Mathlib
import Definitions.Def_DDROCS_SimultaneouslyImplies
import Definitions.Def_DDROCS_PCS
import Definitions.Def_DDROCS_UCS

set_option autoImplicit false

open MeasureTheory InnerProductSpace Matrix

namespace DDROCSaux215

/-- The quadratic form `vᵀAv` written as a double sum. -/
noncomputable def quad {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, ∑ j, v i * A i j * v j

lemma inner_eq_sum {d : ℕ} (v u : EuclideanSpace ℝ (Fin d)) : ⟪v, u⟫_ℝ = ∑ i, v i * u i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma lin_coord {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (Matrix.toEuclideanLin M v) i = ∑ j, M i j * v j := rfl

lemma norm_sq_sum {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) : ‖v‖ ^ 2 = ∑ i, v i * v i := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum]

lemma inner_CT {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (v w : EuclideanSpace ℝ (Fin d)) :
    ⟪v, Matrix.toEuclideanLin Cᵀ w⟫_ℝ = ⟪Matrix.toEuclideanLin C v, w⟫_ℝ := by
  rw [inner_eq_sum, inner_eq_sum]
  simp only [lin_coord, transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma norm_C_sq {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    ‖Matrix.toEuclideanLin C v‖ ^ 2 = quad (Cᵀ * C) v := by
  rw [norm_sq_sum]
  simp only [quad, lin_coord, Matrix.mul_apply, transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

lemma quad_add {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    quad (A + B) v = quad A v + quad B v := by
  simp only [quad, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma quad_sub {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    quad (A - B) v = quad A v - quad B v := by
  simp only [quad, Matrix.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma quad_smul_one {d : ℕ} (c : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    quad (c • (1 : Matrix (Fin d) (Fin d) ℝ)) v = c * ‖v‖ ^ 2 := by
  rw [norm_sq_sum, Finset.mul_sum]
  simp only [quad, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  ring

lemma quad_le_frob {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    quad A v ≤ DDROCS.frobNorm A * ‖v‖ ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d × Fin d))
    (fun p => A p.1 p.2) (fun p => v p.1 * v p.2)
  have h1 : (∑ p : Fin d × Fin d, A p.1 p.2 * (v p.1 * v p.2)) = quad A v := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : (∑ p : Fin d × Fin d, A p.1 p.2 ^ 2) = ∑ i, ∑ j, A i j ^ 2 := Fintype.sum_prod_type _
  have h3 : (∑ p : Fin d × Fin d, (v p.1 * v p.2) ^ 2) = (‖v‖ ^ 2) ^ 2 := by
    rw [Fintype.sum_prod_type, norm_sq_sum, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2, h3] at hcs
  have habs := Real.abs_le_sqrt hcs
  have hF : (0:ℝ) ≤ ∑ i, ∑ j, A i j ^ 2 := by positivity
  rw [Real.sqrt_mul hF, Real.sqrt_sq (sq_nonneg _)] at habs
  unfold DDROCS.frobNorm
  exact (le_abs_self _).trans habs

/-- Support function of `U^CS_ε`, attained. -/
lemma isGreatest_UCS {d : ℕ} (μ : EuclideanSpace ℝ (Fin d)) (Γ₁ : ℝ) (hΓ : 0 ≤ Γ₁)
    (C : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    IsGreatest ((fun u => ⟪v, u⟫_ℝ) '' DDROCS.UCS μ Γ₁ C ε)
      (⟪v, μ⟫_ℝ + Γ₁ * ‖v‖ + Real.sqrt (1 / ε - 1) * ‖Matrix.toEuclideanLin C v‖) := by
  set r := Real.sqrt (1 / ε - 1) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  set z := Matrix.toEuclideanLin C v with hz
  constructor
  · refine ⟨μ + (Γ₁ / ‖v‖) • v + Matrix.toEuclideanLin Cᵀ ((r / ‖z‖) • z),
      ⟨(Γ₁ / ‖v‖) • v, (r / ‖z‖) • z, ?_, ?_, rfl⟩, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hΓ (norm_nonneg _))]
      rcases eq_or_ne ‖v‖ 0 with h | h
      · rw [h, mul_zero]; exact hΓ
      · rw [div_mul_cancel₀ _ h]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr0 (norm_nonneg _))]
      rcases eq_or_ne ‖z‖ 0 with h | h
      · rw [h, mul_zero]; exact hr0
      · rw [div_mul_cancel₀ _ h]
    · simp only
      rw [inner_add_right, inner_add_right, inner_CT, ← hz, real_inner_smul_right,
        real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      have e1 : Γ₁ / ‖v‖ * ‖v‖ ^ 2 = Γ₁ * ‖v‖ := by
        rcases eq_or_ne ‖v‖ 0 with h | h
        · rw [h]; ring
        · field_simp
      have e2 : r / ‖z‖ * ‖z‖ ^ 2 = r * ‖z‖ := by
        rcases eq_or_ne ‖z‖ 0 with h | h
        · rw [h]; ring
        · field_simp
      rw [e1, e2]
  · rintro _ ⟨u, ⟨y, w, hy, hw, rfl⟩, rfl⟩
    simp only
    rw [inner_add_right, inner_add_right, inner_CT, ← hz]
    have h1 : ⟪v, y⟫_ℝ ≤ Γ₁ * ‖v‖ :=
      (real_inner_le_norm v y).trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hy (norm_nonneg _))
    have h2 : ⟪z, w⟫_ℝ ≤ r * ‖z‖ :=
      (real_inner_le_norm z w).trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hw (norm_nonneg _))
    linarith

lemma convex_UCS {d : ℕ} (μ : EuclideanSpace ℝ (Fin d)) (Γ₁ : ℝ)
    (C : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) : Convex ℝ (DDROCS.UCS μ Γ₁ C ε) := by
  rintro _ ⟨y1, w1, hy1, hw1, rfl⟩ _ ⟨y2, w2, hy2, hw2, rfl⟩ a b ha hb hab
  refine ⟨a • y1 + b • y2, a • w1 + b • w2, ?_, ?_, ?_⟩
  · calc ‖a • y1 + b • y2‖ ≤ ‖a • y1‖ + ‖b • y2‖ := norm_add_le _ _
      _ = a * ‖y1‖ + b * ‖y2‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
            abs_of_nonneg hb]
      _ ≤ a * Γ₁ + b * Γ₁ := by gcongr
      _ = Γ₁ := by rw [← add_mul, hab, one_mul]
  · calc ‖a • w1 + b • w2‖ ≤ ‖a • w1‖ + ‖b • w2‖ := norm_add_le _ _
      _ = a * ‖w1‖ + b * ‖w2‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
            abs_of_nonneg hb]
      _ ≤ a * Real.sqrt (1 / ε - 1) + b * Real.sqrt (1 / ε - 1) := by gcongr
      _ = Real.sqrt (1 / ε - 1) := by rw [← add_mul, hab, one_mul]
  · rw [map_add, map_smul, map_smul]
    obtain rfl : b = 1 - a := by linarith
    module

section prob

variable {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]

lemma ae_ball (R : ℝ) (h : P (Metric.closedBall 0 R) = 1) : ∀ᵐ u ∂P, ‖u‖ ≤ R := by
  have h0 : P (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R)ᶜ = 0 :=
    (prob_compl_eq_zero_iff Metric.isClosed_closedBall.measurableSet).mpr h
  rw [ae_iff]
  refine measure_mono_null (fun u hu => ?_) h0
  simp only [Set.mem_ofPred_eq, not_le] at hu
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
  exact hu

lemma cont_coord (i : Fin d) : Continuous (fun u : EuclideanSpace ℝ (Fin d) => u i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous

lemma integ_id (R : ℝ) (hb : ∀ᵐ u ∂P, ‖u‖ ≤ R) : Integrable (fun u => u) P :=
  Integrable.of_bound continuous_id.aestronglyMeasurable R hb

lemma integ_prod (R : ℝ) (hb : ∀ᵐ u ∂P, ‖u‖ ≤ R) (i j : Fin d) :
    Integrable (fun u : EuclideanSpace ℝ (Fin d) => u i * u j) P := by
  refine Integrable.of_bound ((cont_coord i).mul (cont_coord j)).aestronglyMeasurable (R * R) ?_
  filter_upwards [hb] with u hu
  have hi : ‖u i‖ ≤ R := (PiLp.norm_apply_le u i).trans hu
  have hj : ‖u j‖ ≤ R := (PiLp.norm_apply_le u j).trans hu
  rw [norm_mul]
  exact mul_le_mul hi hj (norm_nonneg _) ((norm_nonneg _).trans hi)

lemma integ_X (R : ℝ) (hb : ∀ᵐ u ∂P, ‖u‖ ≤ R) (v : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun u => ⟪v, u⟫_ℝ) P := by
  refine Integrable.of_bound (continuous_const.inner continuous_id).aestronglyMeasurable
    (‖v‖ * R) ?_
  filter_upwards [hb] with u hu
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm v u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))

lemma integ_X2 (R : ℝ) (hb : ∀ᵐ u ∂P, ‖u‖ ≤ R) (v : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun u => ⟪v, u⟫_ℝ ^ 2) P := by
  refine Integrable.of_bound ((continuous_const.inner continuous_id).pow 2).aestronglyMeasurable
    ((‖v‖ * R) ^ 2) ?_
  filter_upwards [hb] with u hu
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _)
    ((abs_real_inner_le_norm v u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))) 2

lemma coord_integral (R : ℝ) (hb : ∀ᵐ u ∂P, ‖u‖ ≤ R) (i : Fin d) :
    ∫ u, u i ∂P = (∫ u, u ∂P) i := by
  have := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm (integ_id P R hb)
  simpa using this

lemma Q_eq (R : ℝ) (hb : ∀ᵐ u ∂P, ‖u‖ ≤ R) (v : EuclideanSpace ℝ (Fin d)) :
    (∫ u, ⟪v, u⟫_ℝ ^ 2 ∂P) - (∫ u, ⟪v, u⟫_ℝ ∂P) ^ 2 = quad (DDROCS.covMat P) v := by
  have hX2 : (fun u : EuclideanSpace ℝ (Fin d) => ⟪v, u⟫_ℝ ^ 2) =
      fun u => ∑ i, ∑ j, (v i * v j) * (u i * u j) := by
    funext u
    rw [inner_eq_sum, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hX : (fun u : EuclideanSpace ℝ (Fin d) => ⟪v, u⟫_ℝ) = fun u => ∑ i, v i * u i := by
    funext u; exact inner_eq_sum v u
  have hcoord : ∀ i, Integrable (fun u : EuclideanSpace ℝ (Fin d) => u i) P := fun i =>
    Integrable.of_bound (cont_coord i).aestronglyMeasurable R (by
      filter_upwards [hb] with u hu; exact (PiLp.norm_apply_le u i).trans hu)
  rw [hX2, hX, integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (integ_prod P R hb i j).const_mul _)),
    integral_finsetSum _ (fun i _ => (hcoord i).const_mul _)]
  have hin : ∀ i, ∫ u, ∑ j, v i * v j * (u i * u j) ∂P = ∑ j, v i * v j * ∫ u, u i * u j ∂P := by
    intro i
    rw [integral_finsetSum _ (fun j _ => (integ_prod P R hb i j).const_mul _)]
    simp only [integral_const_mul]
  simp only [hin, integral_const_mul]
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  unfold quad DDROCS.covMat
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Cantelli's one-sided Chebyshev inequality, in the form needed. -/
lemma cantelli (X : EuclideanSpace ℝ (Fin d) → ℝ)
    (hX : Integrable X P) (hX2 : Integrable (fun u => X u ^ 2) P)
    (s : ℝ) (hs : 0 ≤ s) (hQ : (∫ u, X u ^ 2 ∂P) - (∫ u, X u ∂P) ^ 2 ≤ s ^ 2)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    P.real {u | (∫ u, X u ∂P) + Real.sqrt (1 / ε - 1) * s < X u} ≤ ε := by
  set m := ∫ u, X u ∂P with hm
  set r := Real.sqrt (1 / ε - 1) with hr
  have hY : ∀ a : ℝ, Integrable (fun u => (X u - m + a) ^ 2) P ∧
      ∫ u, (X u - m + a) ^ 2 ∂P = ((∫ u, X u ^ 2 ∂P) - m ^ 2) + a ^ 2 := by
    intro a
    have he : (fun u => (X u - m + a) ^ 2) =
        fun u => (X u ^ 2 + (2 * (a - m)) * X u) + (a - m) ^ 2 := by
      funext u; ring
    have hi1 : Integrable (fun u => X u ^ 2 + (2 * (a - m)) * X u) P :=
      hX2.add (hX.const_mul _)
    refine ⟨by rw [he]; exact hi1.add (integrable_const _), ?_⟩
    rw [he, integral_add hi1 (integrable_const _), integral_add hX2 (hX.const_mul _),
      integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul, ← hm]
    ring
  rcases hs.lt_or_eq with hpos | hzero
  · have hr2 : r ^ 2 = 1 / ε - 1 := Real.sq_sqrt (by
      rw [sub_nonneg, le_div_iff₀ hε0]; linarith)
    have hrpos : 0 < r := Real.sqrt_pos.mpr (by
      rw [sub_pos, lt_div_iff₀ hε0]; linarith)
    have hεr : ε * r ^ 2 = 1 - ε := by rw [hr2]; field_simp
    set a := s / r with ha
    have har : a * r = s := by rw [ha]; field_simp
    have hapos : 0 < a := div_pos hpos hrpos
    obtain ⟨hYi, hYv⟩ := hY a
    have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (fun u => sq_nonneg (X u - m + a)))
      hYi ((r * s + a) ^ 2)
    have hsub : {u | m + r * s < X u} ⊆ {u | (r * s + a) ^ 2 ≤ (X u - m + a) ^ 2} := by
      intro u hu
      simp only [Set.mem_ofPred_eq] at hu ⊢
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hmono := measureReal_mono (μ := P) hsub (measure_ne_top _ _)
    have hpos2 : 0 < (r * s + a) ^ 2 := by positivity
    have hid : ε * (r * s + a) ^ 2 = s ^ 2 + a ^ 2 := by
      rw [← har]; linear_combination (a ^ 2 * (r ^ 2 + 1)) * hεr
    have h1 : (r * s + a) ^ 2 * P.real {u | m + r * s < X u} ≤ ε * (r * s + a) ^ 2 := by
      rw [hid]
      calc (r * s + a) ^ 2 * P.real {u | m + r * s < X u}
          ≤ (r * s + a) ^ 2 * P.real {u | (r * s + a) ^ 2 ≤ (X u - m + a) ^ 2} :=
            mul_le_mul_of_nonneg_left hmono hpos2.le
        _ ≤ _ := hmk
        _ = _ := hYv
        _ ≤ s ^ 2 + a ^ 2 := by linarith
    rw [mul_comm ε] at h1
    exact le_of_mul_le_mul_left h1 hpos2
  · subst hzero
    obtain ⟨hYi, hYv⟩ := hY 0
    have hint0 : ∫ u, (X u - m + 0) ^ 2 ∂P = 0 :=
      le_antisymm (by rw [hYv]; linarith) (integral_nonneg fun u => sq_nonneg _)
    have hae := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg (X u - m + 0)) hYi).mp hint0
    have hnull : P {u | m + r * 0 < X u} = 0 := by
      rw [Filter.EventuallyEq, ae_iff] at hae
      refine measure_mono_null (fun u hu => ?_) hae
      simp only [Set.mem_ofPred_eq, mul_zero, add_zero, Pi.zero_apply] at hu ⊢
      intro h0
      have : X u - m = 0 := by nlinarith [sq_nonneg (X u - m)]
      linarith
    rw [measureReal_def, hnull, ENNReal.toReal_zero]
    exact hε0.le

end prob

lemma tail {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P] (R : ℝ)
    (μ : EuclideanSpace ℝ (Fin d)) (Sig : Matrix (Fin d) (Fin d) ℝ) (Γ₁ Γ₂ : ℝ)
    (C : Matrix (Fin d) (Fin d) ℝ) (hC : Cᵀ * C = Sig + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hP : P ∈ DDROCS.PCS R μ Sig Γ₁ Γ₂) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : EuclideanSpace ℝ (Fin d)) :
    P.real {u | ⟪v, μ⟫_ℝ + Γ₁ * ‖v‖ + Real.sqrt (1 / ε - 1) * ‖Matrix.toEuclideanLin C v‖
      < ⟪v, u⟫_ℝ} ≤ ε := by
  obtain ⟨_, hball, hmean, hfrob⟩ := hP
  have hb := ae_ball P R hball
  have hc := cantelli P (fun u => ⟪v, u⟫_ℝ) (integ_X P R hb v) (integ_X2 P R hb v)
    ‖Matrix.toEuclideanLin C v‖ (norm_nonneg _) ?_ ε hε0 hε1
  · refine le_trans (measureReal_mono (fun u hu => ?_) (measure_ne_top _ _)) hc
    simp only [Set.mem_ofPred_eq] at hu ⊢
    have hm : ∫ u, ⟪v, u⟫_ℝ ∂P = ⟪v, ∫ u, u ∂P⟫_ℝ := integral_inner (integ_id P R hb) v
    have h1 : ⟪v, ∫ u, u ∂P⟫_ℝ ≤ ⟪v, μ⟫_ℝ + Γ₁ * ‖v‖ := by
      have : ⟪v, ∫ u, u ∂P⟫_ℝ = ⟪v, μ⟫_ℝ + ⟪v, (∫ u, u ∂P) - μ⟫_ℝ := by
        rw [inner_sub_right]; ring
      rw [this]
      have := (real_inner_le_norm v ((∫ u, u ∂P) - μ)).trans
        (mul_le_mul_of_nonneg_left hmean (norm_nonneg v))
      linarith
    rw [hm]; linarith
  · rw [Q_eq P R hb v, norm_C_sq, hC, quad_add, quad_smul_one]
    have hsplit : DDROCS.covMat P = (DDROCS.covMat P - Sig) + Sig := by abel
    rw [hsplit, quad_add]
    have := (quad_le_frob (DDROCS.covMat P - Sig) v).trans
      (mul_le_mul_of_nonneg_right hfrob (sq_nonneg ‖v‖))
    linarith

lemma guarantee {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P] (R : ℝ)
    (μ : EuclideanSpace ℝ (Fin d)) (Sig : Matrix (Fin d) (Fin d) ℝ) (Γ₁ Γ₂ : ℝ) (hΓ : 0 ≤ Γ₁)
    (C : Matrix (Fin d) (Fin d) ℝ) (hC : Cᵀ * C = Sig + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hP : P ∈ DDROCS.PCS R μ Sig Γ₁ Γ₂) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    DDROCS.ImpliesGuarantee (DDROCS.UCS μ Γ₁ C ε) P ε := by
  intro g hg hle
  have hgc : Continuous g := continuousOn_univ.mp (hg.continuousOn isOpen_univ)
  have hAconv : Convex ℝ {x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) | 0 < g x} :=
    hg.convex_gt 0
  have hAopen : IsOpen {x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) | 0 < g x} := by
    simpa only [Set.mem_univ, true_and, Set.sep_univ] using isOpen_lt continuous_const hgc
  have hdisj : Disjoint {x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) | 0 < g x}
      (DDROCS.UCS μ Γ₁ C ε) := by
    rw [Set.disjoint_left]
    rintro a ⟨_, ha⟩ hU
    exact absurd (hle a hU) (not_le.mpr ha)
  obtain ⟨φ, s, hA, hB⟩ := geometric_hahn_banach_open hAconv hAopen (convex_UCS μ Γ₁ C ε) hdisj
  set z := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm φ with hz
  have hφ : ∀ x, φ x = ⟪z, x⟫_ℝ := fun x => (InnerProductSpace.toDual_symm_apply).symm
  set v := -z with hv
  set δ := ⟪v, μ⟫_ℝ + Γ₁ * ‖v‖ + Real.sqrt (1 / ε - 1) * ‖Matrix.toEuclideanLin C v‖ with hδ
  have hδs : δ ≤ -s := by
    obtain ⟨b, hbU, hbδ⟩ := (isGreatest_UCS μ Γ₁ hΓ C ε v).1
    have := hB b hbU
    rw [hφ] at this
    simp only at hbδ
    rw [← hδ, hv, inner_neg_left] at hbδ
    rw [← hbδ]
    linarith
  have hsub : {u | ⟪v, u⟫_ℝ ≤ δ} ⊆ {u | g u ≤ 0} := by
    intro u hu
    simp only [Set.mem_ofPred_eq] at hu ⊢
    by_contra hpos
    push Not at hpos
    have h1 := hA u ⟨Set.mem_univ _, hpos⟩
    rw [hφ] at h1
    rw [hv, inner_neg_left] at hu
    linarith
  have hmeas : MeasurableSet {u : EuclideanSpace ℝ (Fin d) | ⟪v, u⟫_ℝ ≤ δ} :=
    measurableSet_le (continuous_const.inner continuous_id).measurable measurable_const
  have hcompl := measureReal_add_measureReal_compl (μ := P) hmeas
  rw [probReal_univ] at hcompl
  have hc : {u : EuclideanSpace ℝ (Fin d) | ⟪v, u⟫_ℝ ≤ δ}ᶜ = {u | δ < ⟪v, u⟫_ℝ} := by
    ext u; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  rw [hc] at hcompl
  have ht : P.real {u | δ < ⟪v, u⟫_ℝ} ≤ ε := tail P R μ Sig Γ₁ Γ₂ C hC hP ε hε0 hε1 v
  have hm := measureReal_mono (μ := P) hsub (measure_ne_top _ _)
  show 1 - ε ≤ P.real {u | g u ≤ 0}
  linarith

end DDROCSaux215

open MeasureTheory InnerProductSpace Matrix DDROCS in
theorem solution {d N : ℕ} (Pstar : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure Pstar] (α R : ℝ)
    (μhat : (Fin N → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (Sigmahat : (Fin N → EuclideanSpace ℝ (Fin d)) → Matrix (Fin d) (Fin d) ℝ)
    (Γ₁ Γ₂ : (Fin N → EuclideanSpace ℝ (Fin d)) → ℝ) (hΓ₁ : ∀ S, 0 ≤ Γ₁ S)
    (C : (Fin N → EuclideanSpace ℝ (Fin d)) → Matrix (Fin d) (Fin d) ℝ)
    (hC : ∀ S, (C S)ᵀ * C S = Sigmahat S + Γ₂ S • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hcov : 1 - α ≤ (Measure.pi (fun _ : Fin N => Pstar)
      {S | Pstar ∈ PCS R (μhat S) (Sigmahat S) (Γ₁ S) (Γ₂ S)}).toReal) :
    1 - α ≤ (Measure.pi (fun _ : Fin N => Pstar)
      {S | SimultaneouslyImplies (fun ε => UCS (μhat S) (Γ₁ S) (C S) ε) Pstar}).toReal ∧
    ∀ S : Fin N → EuclideanSpace ℝ (Fin d), ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ v : EuclideanSpace ℝ (Fin d),
        IsLUB ((fun u => ⟪v, u⟫_ℝ) '' UCS (μhat S) (Γ₁ S) (C S) ε)
          (⟪μhat S, v⟫_ℝ + Γ₁ S * ‖v‖ + Real.sqrt ((1 - ε) / ε) *
            Real.sqrt (∑ i, ∑ j,
              v i * (Sigmahat S + Γ₂ S • (1 : Matrix (Fin d) (Fin d) ℝ)) i j * v j)) := by
  constructor
  · have hsub : {S : Fin N → EuclideanSpace ℝ (Fin d) |
        Pstar ∈ PCS R (μhat S) (Sigmahat S) (Γ₁ S) (Γ₂ S)} ⊆
        {S | SimultaneouslyImplies (fun ε => UCS (μhat S) (Γ₁ S) (C S) ε) Pstar} := by
      intro S hS ε hε0 hε1
      exact DDROCSaux215.guarantee Pstar R (μhat S) (Sigmahat S) (Γ₁ S) (Γ₂ S) (hΓ₁ S) (C S)
        (hC S) hS ε hε0 hε1
    exact hcov.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub))
  · intro S ε hε0 hε1 v
    have hq : (∑ i, ∑ j, v i * (Sigmahat S + Γ₂ S • (1 : Matrix (Fin d) (Fin d) ℝ)) i j * v j)
        = ‖Matrix.toEuclideanLin (C S) v‖ ^ 2 := by
      rw [DDROCSaux215.norm_C_sq, hC S]; rfl
    have he : (1 - ε) / ε = 1 / ε - 1 := by field_simp
    rw [hq, Real.sqrt_sq (norm_nonneg _), he, real_inner_comm]
    exact (DDROCSaux215.isGreatest_UCS (μhat S) (Γ₁ S) (hΓ₁ S) (C S) ε v).isLUB
