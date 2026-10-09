-- Prove2me | solution 1 for GaussianMatrix.chevet_expectation_bound
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T07:25:08.498337+00:00
-- url     : https://prove2.me/submissions/142da036-99a5-43b8-87c8-b5a22f1a8320

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_spectral_second_moment_bound

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma cebSol_measurePreserving_coord {p m : ℕ} (a : Fin p) (b : Fin m) :
    MeasurePreserving (fun G : Fin p → Fin m → ℝ => G a b) (gaussianMatrix p m)
      (gaussianReal 0 1) :=
  (measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) b).comp
    (measurePreserving_eval (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal 0 1) a)

/-- `‖G‖_F² = ∑ᵢⱼ Gᵢⱼ²` is integrable under the Gaussian matrix law. -/
lemma cebSol_integrable_frobSq (p m : ℕ) :
    Integrable (fun X : Fin p → Fin m → ℝ => frobSq (Matrix.of X)) (gaussianMatrix p m) := by
  unfold frobSq
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  simp only [Matrix.of_apply]
  exact ((memLp_id_gaussianReal' 2 (by simp)).comp_measurePreserving
    (cebSol_measurePreserving_coord i j)).integrable_sq

lemma cebSol_frobSq_nonneg {p m : ℕ} (X : Fin p → Fin m → ℝ) : 0 ≤ frobSq (Matrix.of X) :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma cebSol_continuous_frobNorm (p m : ℕ) :
    Continuous (fun X : Fin p → Fin m → ℝ => frobNorm (Matrix.of X)) := by
  unfold frobNorm frobSq
  simp only [Matrix.of_apply]
  fun_prop

/-- A function that is `L`-Lipschitz for the Frobenius norm is continuous. -/
lemma cebSol_continuous_of_lip {p m : ℕ} (h : (Fin p → Fin m → ℝ) → ℝ) (L : ℝ)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (Matrix.of X - Matrix.of Y)) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro X₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hc : Continuous (fun Y : Fin p → Fin m → ℝ => L * frobNorm (Matrix.of (Y - X₀))) :=
    continuous_const.mul ((cebSol_continuous_frobNorm p m).comp (continuous_id.sub
      continuous_const))
  have h0 : Filter.Tendsto (fun Y : Fin p → Fin m → ℝ => L * frobNorm (Matrix.of (Y - X₀)))
      (nhds X₀) (nhds 0) := by
    have := hc.tendsto X₀
    simpa [frobNorm, frobSq] using this
  refine squeeze_zero (fun _ => dist_nonneg) (fun Y => ?_) h0
  rw [Real.dist_eq]
  have := hLip Y X₀
  simpa [Matrix.of_sub_of] using this

/-- A function that is `L`-Lipschitz for the Frobenius norm is integrable, with integrable
square, under the Gaussian matrix law. -/
lemma cebSol_integrable_of_lip {p m : ℕ} (h : (Fin p → Fin m → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (Matrix.of X - Matrix.of Y)) :
    Integrable h (gaussianMatrix p m) ∧
      Integrable (fun X => h X ^ 2) (gaussianMatrix p m) := by
  have hcont := cebSol_continuous_of_lip h L hLip
  have hF := cebSol_integrable_frobSq p m
  have hbound : ∀ X, |h X| ≤ |h 0| + L * frobNorm (Matrix.of X) := by
    intro X
    have h1 := hLip X 0
    have h2 : Matrix.of X - Matrix.of (0 : Fin p → Fin m → ℝ) = Matrix.of X := by
      ext i j; simp
    rw [h2] at h1
    have := abs_sub_abs_le_abs_sub (h X) (h 0)
    linarith
  have hsq : ∀ X : Fin p → Fin m → ℝ, frobNorm (Matrix.of X) ^ 2 = frobSq (Matrix.of X) := fun X =>
    Real.sq_sqrt (cebSol_frobSq_nonneg X)
  have hfn : ∀ X : Fin p → Fin m → ℝ, 0 ≤ frobNorm (Matrix.of X) := fun X => Real.sqrt_nonneg _
  constructor
  · refine Integrable.mono' (((integrable_const (|h 0| + L)).add (hF.const_mul L)))
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs]
    refine (hbound X).trans ?_
    have := hsq X
    have := hfn X
    have : frobNorm (Matrix.of X) ≤ 1 + frobSq (Matrix.of X) := by
      nlinarith [sq_nonneg (frobNorm (Matrix.of X) - 1)]
    simp only [Pi.add_apply]
    nlinarith
  · refine Integrable.mono' (((integrable_const (2 * h 0 ^ 2)).add (hF.const_mul (2 * L ^ 2))))
      (hcont.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    have hb := hbound X
    have h0 : 0 ≤ |h X| := abs_nonneg _
    have : |h X| ^ 2 ≤ (|h 0| + L * frobNorm (Matrix.of X)) ^ 2 := pow_le_pow_left₀ h0 hb 2
    rw [sq_abs] at this
    simp only [Pi.add_apply]
    have hs := hsq X
    nlinarith [sq_nonneg (|h 0| - L * frobNorm (Matrix.of X)), sq_abs (h 0)]

/-- Row-wise Cauchy–Schwarz: `‖B x‖₂² ≤ ‖B‖_F² ‖x‖₂²`. -/
lemma cebSol_mulVec_dot_le {m n : Type*} [Fintype m] [Fintype n]
    (B : Matrix m n ℝ) (x : n → ℝ) :
    (B *ᵥ x) ⬝ᵥ (B *ᵥ x) ≤ frobSq B * (x ⬝ᵥ x) := by
  unfold frobSq
  simp only [dotProduct, Matrix.mulVec]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => B i j) x
  calc (∑ j, B i j * x j) * (∑ j, B i j * x j) = (∑ j, B i j * x j) ^ 2 := by ring
    _ ≤ (∑ j, B i j ^ 2) * ∑ j, x j ^ 2 := h
    _ = (∑ j, B i j ^ 2) * ∑ j, x j * x j := by simp only [sq]

lemma cebSol_frobSq_nonneg' {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℝ) :
    0 ≤ frobSq B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma cebSol_euclid_norm {n : Type*} [Fintype n] (v : EuclideanSpace ℝ n) :
    ‖v‖ = Real.sqrt (v.ofLp ⬝ᵥ v.ofLp) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, sq]

open scoped Matrix.Norms.L2Operator in
/-- The `ℓ₂ → ℓ₂` operator norm is at most the Frobenius norm. -/
lemma cebSol_specNorm_le_frobNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (B : Matrix m n ℝ) : specNorm B ≤ frobNorm B := by
  unfold specNorm
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  show ‖(Matrix.toEuclideanLin B x)‖ ≤ frobNorm B * ‖x‖
  rw [cebSol_euclid_norm, cebSol_euclid_norm, frobNorm, ← Real.sqrt_mul
    (cebSol_frobSq_nonneg' B)]
  exact Real.sqrt_le_sqrt (cebSol_mulVec_dot_le B x.ofLp)

open scoped Matrix.Norms.L2Operator in
/-- `G ↦ ‖S G T‖` is `‖S‖‖T‖`-Lipschitz for the Frobenius norm. -/
lemma cebSol_sandwich_lip {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) (X Y : Fin p → Fin m → ℝ) :
    |specNorm (S * Matrix.of X * T) - specNorm (S * Matrix.of Y * T)|
      ≤ (specNorm S * specNorm T) * frobNorm (Matrix.of X - Matrix.of Y) := by
  unfold specNorm
  refine (abs_norm_sub_norm_le _ _).trans ?_
  have hd : S * Matrix.of X * T - S * Matrix.of Y * T = S * (Matrix.of X - Matrix.of Y) * T := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hd]
  have h1 := Matrix.l2_opNorm_mul (S * (Matrix.of X - Matrix.of Y)) T
  have h2 := Matrix.l2_opNorm_mul S (Matrix.of X - Matrix.of Y)
  have h3 := cebSol_specNorm_le_frobNorm (Matrix.of X - Matrix.of Y)
  unfold specNorm at h3
  have hS : 0 ≤ ‖S‖ := norm_nonneg _
  have hT : 0 ≤ ‖T‖ := norm_nonneg _
  have hD : 0 ≤ ‖Matrix.of X - Matrix.of Y‖ := norm_nonneg _
  calc ‖S * (Matrix.of X - Matrix.of Y) * T‖
      ≤ ‖S * (Matrix.of X - Matrix.of Y)‖ * ‖T‖ := h1
    _ ≤ (‖S‖ * ‖Matrix.of X - Matrix.of Y‖) * ‖T‖ := mul_le_mul_of_nonneg_right h2 hT
    _ ≤ (‖S‖ * frobNorm (Matrix.of X - Matrix.of Y)) * ‖T‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hS) hT
    _ = (‖S‖ * ‖T‖) * frobNorm (Matrix.of X - Matrix.of Y) := by ring

open scoped Matrix.Norms.L2Operator in
lemma cebSol_specNorm_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (B : Matrix m n ℝ) : 0 ≤ specNorm B := norm_nonneg _

/-- `𝔼 X ≤ (𝔼 X² / δ + δ) / 2` for every `δ > 0` (from `2δx ≤ x² + δ²`). -/
lemma cebSol_integral_le_of_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ) (δ : ℝ) (hδ : 0 < δ) :
    ∫ ω, X ω ∂μ ≤ ((∫ ω, X ω ^ 2 ∂μ) / δ + δ) / 2 := by
  have hI : Integrable (fun ω => (X ω ^ 2 / δ + δ) / 2) μ :=
    ((hX2.div_const δ).add (integrable_const δ)).div_const 2
  have hpt : ∀ ω, X ω ≤ (X ω ^ 2 / δ + δ) / 2 := by
    intro ω
    rw [div_add' _ _ _ hδ.ne', div_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (X ω - δ)]
  refine (integral_mono hX hI hpt).trans (le_of_eq ?_)
  rw [integral_div, integral_add (hX2.div_const δ) (integrable_const δ), integral_div,
    integral_const]
  simp

/-- Jensen (Cauchy–Schwarz) in the form: `𝔼 X² ≤ c²` with `c ≥ 0` implies `𝔼 X ≤ c`. -/
lemma cebSol_integral_le_of_integral_sq_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∫ ω, X ω ^ 2 ∂μ ≤ c ^ 2) : ∫ ω, X ω ∂μ ≤ c := by
  rcases hc.lt_or_eq with hc | hc
  · refine (cebSol_integral_le_of_sq μ X hX hX2 c hc).trans ?_
    have : (∫ ω, X ω ^ 2 ∂μ) / c ≤ c := by
      rw [div_le_iff₀ hc]; nlinarith
    linarith
  · subst hc
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    refine (cebSol_integral_le_of_sq μ X hX hX2 δ hδ).trans ?_
    have : (∫ ω, X ω ^ 2 ∂μ) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by simpa using h) hδ.le
    linarith

lemma cebSol_frobNorm_nonneg {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℝ) :
    0 ≤ frobNorm B := Real.sqrt_nonneg _

end GaussianMatrix

open GaussianMatrix

theorem solution {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) :
    ∫ G, specNorm (S * Matrix.of G * T) ∂(gaussianMatrix p m)
      ≤ specNorm S * frobNorm T + frobNorm S * specNorm T := by
  obtain ⟨hI, hI2⟩ := cebSol_integrable_of_lip
    (fun G : Fin p → Fin m → ℝ => specNorm (S * Matrix.of G * T))
    (specNorm S * specNorm T) (mul_nonneg (cebSol_specNorm_nonneg S) (cebSol_specNorm_nonneg T))
    (cebSol_sandwich_lip S T)
  refine cebSol_integral_le_of_integral_sq_le (gaussianMatrix p m) _ hI hI2 _ ?_
    (spectral_second_moment_bound S T)
  exact add_nonneg (mul_nonneg (cebSol_specNorm_nonneg S) (cebSol_frobNorm_nonneg T))
    (mul_nonneg (cebSol_frobNorm_nonneg S) (cebSol_specNorm_nonneg T))
