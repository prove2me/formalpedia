-- Prove2me | solution 1 for GaussianMatrix.gordon
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T07:27:35.693388+00:00
-- url     : https://prove2.me/submissions/f8949564-d2e8-429e-a9cc-53f39d99c5da

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_sMin_lipschitz
import Theorems.Thm_GaussianMatrix_specNorm_lipschitz
import Theorems.Thm_GaussianMatrix_gordon_upper
import Theorems.Thm_GaussianMatrix_gordon_lower

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma gordonSol_measurePreserving_coord {p m : ℕ} (a : Fin p) (b : Fin m) :
    MeasurePreserving (fun G : Fin p → Fin m → ℝ => G a b) (gaussianMatrix p m)
      (gaussianReal 0 1) :=
  (measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) b).comp
    (measurePreserving_eval (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal 0 1) a)

/-- `‖G‖_F² = ∑ᵢⱼ Gᵢⱼ²` is integrable under the Gaussian matrix law. -/
lemma gordonSol_integrable_frobSq (p m : ℕ) :
    Integrable (fun X : Fin p → Fin m → ℝ => frobSq (Matrix.of X)) (gaussianMatrix p m) := by
  unfold frobSq
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  simp only [Matrix.of_apply]
  exact ((memLp_id_gaussianReal' 2 (by simp)).comp_measurePreserving
    (gordonSol_measurePreserving_coord i j)).integrable_sq

lemma gordonSol_frobSq_nonneg {p m : ℕ} (X : Fin p → Fin m → ℝ) : 0 ≤ frobSq (Matrix.of X) :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma gordonSol_continuous_frobNorm (p m : ℕ) :
    Continuous (fun X : Fin p → Fin m → ℝ => frobNorm (Matrix.of X)) := by
  unfold frobNorm frobSq
  simp only [Matrix.of_apply]
  fun_prop

/-- A function that is `L`-Lipschitz for the Frobenius norm is continuous. -/
lemma gordonSol_continuous_of_lip {p m : ℕ} (h : (Fin p → Fin m → ℝ) → ℝ) (L : ℝ)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (Matrix.of X - Matrix.of Y)) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro X₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hc : Continuous (fun Y : Fin p → Fin m → ℝ => L * frobNorm (Matrix.of (Y - X₀))) :=
    continuous_const.mul ((gordonSol_continuous_frobNorm p m).comp (continuous_id.sub
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
lemma gordonSol_integrable_of_lip {p m : ℕ} (h : (Fin p → Fin m → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (Matrix.of X - Matrix.of Y)) :
    Integrable h (gaussianMatrix p m) ∧
      Integrable (fun X => h X ^ 2) (gaussianMatrix p m) := by
  have hcont := gordonSol_continuous_of_lip h L hLip
  have hF := gordonSol_integrable_frobSq p m
  have hbound : ∀ X, |h X| ≤ |h 0| + L * frobNorm (Matrix.of X) := by
    intro X
    have h1 := hLip X 0
    have h2 : Matrix.of X - Matrix.of (0 : Fin p → Fin m → ℝ) = Matrix.of X := by
      ext i j; simp
    rw [h2] at h1
    have := abs_sub_abs_le_abs_sub (h X) (h 0)
    linarith
  have hsq : ∀ X : Fin p → Fin m → ℝ, frobNorm (Matrix.of X) ^ 2 = frobSq (Matrix.of X) := fun X =>
    Real.sq_sqrt (gordonSol_frobSq_nonneg X)
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

open scoped Matrix.Norms.L2Operator in
/-- For `n ≥ 1`, the smallest singular value is at most the spectral norm. -/
lemma gordonSol_sMin_le_specNorm {N n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin N) (Fin n) ℝ) :
    sMin A ≤ specNorm A := by
  set x : Fin n → ℝ := Pi.single (⟨0, hn⟩ : Fin n) 1 with hxdef
  have hx : x ⬝ᵥ x = 1 := by
    simp [hxdef, dotProduct, Pi.single_apply]
  have hbdd : BddBelow (Set.range fun y : {x : Fin n → ℝ // x ⬝ᵥ x = 1} =>
      Real.sqrt ((A *ᵥ y.1) ⬝ᵥ (A *ᵥ y.1))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact Real.sqrt_nonneg _
  refine (ciInf_le hbdd ⟨x, hx⟩).trans ?_
  have hop := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  have hnx : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have : ∑ i, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) i‖ ^ 2 = x ⬝ᵥ x := by
      simp [dotProduct, sq]
    rw [this, hx, Real.sqrt_one]
  have hnAx : ‖(EuclideanSpace.equiv (Fin N) ℝ).symm (A *ᵥ x)‖
      = Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp [dotProduct, sq]
  rw [hnx, mul_one] at hop
  simp only at hop
  rw [hnAx] at hop
  exact hop

end GaussianMatrix

open GaussianMatrix

theorem solution {N n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun A : Fin N → Fin n → ℝ => sMin (Matrix.of A)) (gaussianMatrix N n) ∧
    Integrable (fun A : Fin N → Fin n → ℝ => specNorm (Matrix.of A)) (gaussianMatrix N n) ∧
    Real.sqrt N - Real.sqrt n ≤ ∫ A, sMin (Matrix.of A) ∂(gaussianMatrix N n) ∧
    ∫ A, sMin (Matrix.of A) ∂(gaussianMatrix N n)
      ≤ ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) ∧
    ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) ≤ Real.sqrt N + Real.sqrt n := by
  have hI1 := (gordonSol_integrable_of_lip (fun A : Fin N → Fin n → ℝ => sMin (Matrix.of A)) 1
    zero_le_one fun X Y => by
      rw [one_mul]; exact sMin_lipschitz (Matrix.of X) (Matrix.of Y)).1
  have hI2 := (gordonSol_integrable_of_lip (fun A : Fin N → Fin n → ℝ => specNorm (Matrix.of A)) 1
    zero_le_one fun X Y => by
      rw [one_mul]; exact specNorm_lipschitz (Matrix.of X) (Matrix.of Y)).1
  refine ⟨hI1, hI2, gordon_lower hn, ?_, gordon_upper⟩
  exact integral_mono hI1 hI2 fun A => gordonSol_sMin_le_specNorm hn (Matrix.of A)
