-- Prove2me | solution 1 for GaussianMatrix.gordon_lower
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T07:41:44.097571+00:00
-- url     : https://prove2.me/submissions/36a38fb8-f311-47c2-a823-6e3ea19b6572

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_sMin_lipschitz
import Theorems.Thm_GaussianMatrix_specNorm_lipschitz
import Theorems.Thm_GaussianMatrix_gordon_minimax
import Theorems.Thm_GaussianMatrix_expectation_norm_gaussian_diff
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma gl_hasGaussianLaw_pi (κ : Type*) [Fintype κ] :
    HasGaussianLaw (fun x : κ → ℝ => x) (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  have h := iIndepFun.hasGaussianLaw (P := Measure.pi fun _ : κ => gaussianReal 0 1)
    (X := fun k (x : κ → ℝ) => x k) (fun k => ⟨by
      have := (measurePreserving_eval (fun _ : κ => gaussianReal (0 : ℝ) 1) k).map_eq
      rw [this]; infer_instance⟩)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  exact h

lemma gl_hasGaussianLaw_id (p m : ℕ) :
    HasGaussianLaw (fun G : Fin p → Fin m → ℝ => G) (gaussianMatrix p m) := by
  have h := iIndepFun.hasGaussianLaw (P := gaussianMatrix p m)
    (X := fun i (G : Fin p → Fin m → ℝ) => G i) (fun i => ⟨by
      have := (measurePreserving_eval
        (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) i).map_eq
      unfold gaussianMatrix
      rw [this]
      have := (gl_hasGaussianLaw_pi (Fin m)).isGaussian_map
      rwa [Measure.map_id'] at this⟩)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  exact h

lemma gl_measurePreserving_coord {p m : ℕ} (a : Fin p) (b : Fin m) :
    MeasurePreserving (fun G : Fin p → Fin m → ℝ => G a b) (gaussianMatrix p m)
      (gaussianReal 0 1) :=
  (measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) b).comp
    (measurePreserving_eval (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal 0 1) a)

lemma gl_memLp_coord {p m : ℕ} (a : Fin p) (b : Fin m) (q : ENNReal) (hq : q ≠ ⊤) :
    MemLp (fun G : Fin p → Fin m → ℝ => G a b) q (gaussianMatrix p m) :=
  (memLp_id_gaussianReal' q hq).comp_measurePreserving (gl_measurePreserving_coord a b)

lemma gl_integral_comp_coord {p m : ℕ} (a : Fin p) (b : Fin m) (f : ℝ → ℝ)
    (hf : Measurable f) :
    ∫ G, f (G a b) ∂(gaussianMatrix p m) = ∫ x, f x ∂(gaussianReal 0 1) := by
  rw [← (gl_measurePreserving_coord a b).map_eq, integral_map]
  · exact (gl_measurePreserving_coord a b).measurable.aemeasurable
  · exact hf.aestronglyMeasurable

lemma gl_integral_coord {p m : ℕ} (a : Fin p) (b : Fin m) :
    ∫ G, G a b ∂(gaussianMatrix p m) = 0 := by
  have := gl_integral_comp_coord a b (fun x => x) measurable_id
  simpa [integral_id_gaussianReal] using this

lemma gl_integral_coord_sq {p m : ℕ} (a : Fin p) (b : Fin m) :
    ∫ G, G a b ^ 2 ∂(gaussianMatrix p m) = 1 := by
  rw [gl_integral_comp_coord a b (fun x => x ^ 2) (by fun_prop)]
  have h := variance_eq_sub (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp))
  rw [variance_id_gaussianReal] at h
  simp [integral_id_gaussianReal] at h
  exact h.symm

lemma gl_integral_coord_mul {p m : ℕ} (a c : Fin p) (b d : Fin m) :
    ∫ G, G a b * G c d ∂(gaussianMatrix p m) = if a = c ∧ b = d then 1 else 0 := by
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd
      simpa [← pow_two] using gl_integral_coord_sq a b
    · simp only [hbd, and_false, if_false]
      have hrow := measurePreserving_eval
        (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) a
      have h1 : ∫ G, G a b * G a d ∂(gaussianMatrix p m)
          = ∫ x, x b * x d ∂(Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) := by
        have := integral_map (μ := gaussianMatrix p m) hrow.measurable.aemeasurable
          (f := fun x : Fin m → ℝ => x b * x d) (by fun_prop)
        unfold gaussianMatrix at this ⊢
        rw [hrow.map_eq] at this
        exact this.symm
      rw [h1]
      have hind : iIndepFun (fun (i : Fin m) (ω : Fin m → ℝ) => ω i)
          (Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) :=
        iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
      rw [(hind.indepFun hbd).integral_fun_mul_eq_mul_integral
        (measurable_pi_apply b).aestronglyMeasurable (measurable_pi_apply d).aestronglyMeasurable]
      have h0 : ∫ x, x b ∂(Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) = 0 := by
        have hb := measurePreserving_eval (fun _ : Fin m => gaussianReal (0 : ℝ) 1) b
        have := integral_map (μ := Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1)
          hb.measurable.aemeasurable (f := fun x : ℝ => x) (by fun_prop)
        rw [hb.map_eq, integral_id_gaussianReal] at this
        exact this.symm
      simp [h0]
  · simp only [hac, false_and, if_false]
    have hind : iIndepFun (fun (i : Fin p) (ω : Fin p → Fin m → ℝ) => ω i)
        (gaussianMatrix p m) :=
      iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
    have h2 := (hind.indepFun hac).comp (measurable_pi_apply b) (measurable_pi_apply d)
    have := h2.integral_fun_mul_eq_mul_integral
      (by
        have : Measurable (fun ω : Fin p → Fin m → ℝ => ω a b) := by fun_prop
        exact this.aestronglyMeasurable)
      (by
        have : Measurable (fun ω : Fin p → Fin m → ℝ => ω c d) := by fun_prop
        exact this.aestronglyMeasurable)
    simp only [Function.comp_def] at this
    rw [this, gl_integral_coord]
    simp

lemma gl_integrable_coord_mul {p m : ℕ} (a c : Fin p) (b d : Fin m) (k : ℝ) :
    Integrable (fun G : Fin p → Fin m → ℝ => k * (G a b * G c d)) (gaussianMatrix p m) :=
  ((gl_memLp_coord a b 2 (by simp)).integrable_mul (gl_memLp_coord c d 2 (by simp))).const_mul k


noncomputable def glLin {p m : ℕ} (c : Fin p → Fin m → ℝ) (G : Fin p → Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * G i j

/-- The coefficient-to-form map as a continuous linear map into `ι → ℝ`. -/
noncomputable def glLinCLM {ι : Type*} {p m : ℕ} (a : ι → Fin p → Fin m → ℝ) :
    (Fin p → Fin m → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun t => ∑ i, ∑ j,
    a t i j • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => Fin m → ℝ) i))

lemma gl_hasGaussianLaw_lin {ι : Type*} [Fintype ι] {p m : ℕ} (a : ι → Fin p → Fin m → ℝ) :
    HasGaussianLaw (fun G t => glLin (a t) G) (gaussianMatrix p m) := by
  have h := (gl_hasGaussianLaw_id p m).map_fun (glLinCLM a)
  have e : (fun G t => glLin (a t) G) = fun G => glLinCLM a G := by
    funext G t
    simp [glLinCLM, glLin]
  rw [e]; exact h


lemma gl_integrable_lin {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    Integrable (glLin c) (gaussianMatrix p m) := by
  unfold glLin
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((gl_memLp_coord i j 2 (by simp)).integrable (by simp)).const_mul _

lemma gl_continuous_lin {p m : ℕ} (c : Fin p → Fin m → ℝ) : Continuous (glLin c) := by
  unfold glLin; fun_prop

lemma gl_integral_lin {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    ∫ G, glLin c G ∂(gaussianMatrix p m) = 0 := by
  unfold glLin
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((gl_memLp_coord i j 2 (by simp)).integrable (by simp)).const_mul _]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    ((gl_memLp_coord i j 2 (by simp)).integrable (by simp)).const_mul _]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, gl_integral_coord, mul_zero]

lemma gl_lin_sub {p m : ℕ} (c d : Fin p → Fin m → ℝ) (G : Fin p → Fin m → ℝ) :
    glLin c G - glLin d G = glLin (c - d) G := by
  simp only [glLin, ← Finset.sum_sub_distrib, Pi.sub_apply, sub_mul]

lemma gl_integral_lin_sq {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    ∫ G, glLin c G ^ 2 ∂(gaussianMatrix p m) = ∑ i, ∑ j, c i j ^ 2 := by
  have hexp : ∀ G : Fin p → Fin m → ℝ, glLin c G ^ 2 =
      ∑ i, ∑ k, ∑ j, ∑ l, c i j * c k l * (G i j * G k l) := by
    intro G
    unfold glLin
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    gl_integrable_coord_mul i k j l _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    gl_integrable_coord_mul i k j l _]
  rw [Finset.sum_eq_single i]
  · rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
      gl_integrable_coord_mul i i j l _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => gl_integrable_coord_mul i i j l _]
    rw [Finset.sum_eq_single j]
    · rw [integral_const_mul, gl_integral_coord_mul]; simp [sq]
    · intro l _ hl
      rw [integral_const_mul, gl_integral_coord_mul]; simp [Ne.symm hl]
    · simp
  · intro k _ hk
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
      gl_integrable_coord_mul i k j l _]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => gl_integrable_coord_mul i k j l _]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [integral_const_mul, gl_integral_coord_mul]; simp [Ne.symm hk]
  · simp


/-! ### Deterministic part -/

lemma gl_norm_sq_eq {κ : Type*} [Fintype κ] (u : EuclideanSpace ℝ κ) :
    ‖u‖ ^ 2 = ∑ j, u j ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

lemma gl_norm_eq_sqrt {κ : Type*} [Fintype κ] (u : EuclideanSpace ℝ κ) :
    ‖u‖ = Real.sqrt (∑ j, u j ^ 2) := by
  rw [← gl_norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]

open scoped RealInnerProductSpace in
lemma gl_inner_matrix {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (u : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin N)) :
    ⟪v, (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A u⟫
      = ∑ i, ∑ j, v i * A i j * u j := by
  simp [PiLp.inner_apply, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### Probabilistic estimates -/

lemma gl_integrable_iSup {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]
    [Nonempty ι] (f : ι → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) (hm : ∀ t, Measurable (f t)) :
    Integrable (fun ω => ⨆ t, f t ω) μ := by
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun t _ => (hf t).abs)
    (Measurable.iSup hm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_le]
  obtain ⟨t0⟩ := ‹Nonempty ι›
  have hb : BddAbove (Set.range fun t => f t ω) := (Set.finite_range _).bddAbove
  have hs : ∀ t, |f t ω| ≤ ∑ t, |f t ω| := fun t =>
    Finset.single_le_sum (f := fun t => |f t ω|) (fun t _ => abs_nonneg _) (Finset.mem_univ t)
  constructor
  · have h1 := le_ciSup hb t0
    have h2 := hs t0
    have := neg_abs_le (f t0 ω)
    linarith
  · exact ciSup_le fun t => (le_abs_self _).trans (hs t)
/-- Coefficient comparison for unit vectors:
`‖v uᵀ - v' u'ᵀ‖_F² ≤ ‖u - u'‖² + ‖v - v'‖²`. -/
lemma gl_coeff_ineq {N n : ℕ} (u u' : EuclideanSpace ℝ (Fin n)) (v v' : EuclideanSpace ℝ (Fin N))
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) :
    ∑ i, ∑ j, (v i * u j - v' i * u' j) ^ 2 ≤ ∑ j, (u j - u' j) ^ 2 + ∑ i, (v i - v' i) ^ 2 := by
  have su : ∑ j, u j ^ 2 = 1 := by rw [← gl_norm_sq_eq, hu, one_pow]
  have su' : ∑ j, u' j ^ 2 = 1 := by rw [← gl_norm_sq_eq, hu', one_pow]
  have sv : ∑ i, v i ^ 2 = 1 := by rw [← gl_norm_sq_eq, hv, one_pow]
  have sv' : ∑ i, v' i ^ 2 = 1 := by rw [← gl_norm_sq_eq, hv', one_pow]
  set α := ∑ j, u j * u' j with hαdef
  set β := ∑ i, v i * v' i with hβdef
  have hL : ∑ i, ∑ j, (v i * u j - v' i * u' j) ^ 2
      = (∑ i, v i ^ 2) * (∑ j, u j ^ 2) - 2 * (β * α) + (∑ i, v' i ^ 2) * (∑ j, u' j ^ 2) := by
    rw [hαdef, hβdef, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hRu : ∑ j, (u j - u' j) ^ 2 = ∑ j, u j ^ 2 - 2 * α + ∑ j, u' j ^ 2 := by
    rw [hαdef, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hRv : ∑ i, (v i - v' i) ^ 2 = ∑ i, v i ^ 2 - 2 * β + ∑ i, v' i ^ 2 := by
    rw [hβdef, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hα : α ≤ 1 := by
    have : 0 ≤ ∑ j, (u j - u' j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hβ : β ≤ 1 := by
    have : 0 ≤ ∑ i, (v i - v' i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  rw [hL, hRu, hRv, su, su', sv, sv']
  nlinarith [mul_nonneg (sub_nonneg.2 hα) (sub_nonneg.2 hβ)]

/-- Increments of the comparison process `⟨g, u⟩ + ⟨h, v⟩`, written with one Gaussian row
`H₀ ∈ ℝ^{n+N}`. -/
lemma gl_coeffY_sq {N n : ℕ} (u u' : EuclideanSpace ℝ (Fin n)) (v v' : EuclideanSpace ℝ (Fin N)) :
    ∑ _i : Fin 1, ∑ k : Fin (n + N),
      (Fin.append (fun j => u j) (fun i => v i) k - Fin.append (fun j => u' j) (fun i => v' i) k) ^ 2
      = ∑ j, (u j - u' j) ^ 2 + ∑ i, (v i - v' i) ^ 2 := by
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp

/-! ### Integrability -/

/-- `‖G‖_F² = ∑ᵢⱼ Gᵢⱼ²` is integrable under the Gaussian matrix law. -/
lemma gl_integrable_frobSq (p m : ℕ) :
    Integrable (fun X : Fin p → Fin m → ℝ => frobSq (Matrix.of X)) (gaussianMatrix p m) := by
  unfold frobSq
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  simp only [Matrix.of_apply]
  exact ((memLp_id_gaussianReal' 2 (by simp)).comp_measurePreserving
    (gl_measurePreserving_coord i j)).integrable_sq

lemma gl_frobSq_nonneg {p m : ℕ} (X : Fin p → Fin m → ℝ) : 0 ≤ frobSq (Matrix.of X) :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma gl_continuous_frobNorm (p m : ℕ) :
    Continuous (fun X : Fin p → Fin m → ℝ => frobNorm (Matrix.of X)) := by
  unfold frobNorm frobSq
  simp only [Matrix.of_apply]
  fun_prop

/-- A function that is `L`-Lipschitz for the Frobenius norm is continuous. -/
lemma gl_continuous_of_lip {p m : ℕ} (h : (Fin p → Fin m → ℝ) → ℝ) (L : ℝ)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (Matrix.of X - Matrix.of Y)) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro X₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hc : Continuous (fun Y : Fin p → Fin m → ℝ => L * frobNorm (Matrix.of (Y - X₀))) :=
    continuous_const.mul ((gl_continuous_frobNorm p m).comp (continuous_id.sub
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
lemma gl_integrable_of_lip {p m : ℕ} (h : (Fin p → Fin m → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (Matrix.of X - Matrix.of Y)) :
    Integrable h (gaussianMatrix p m) ∧
      Integrable (fun X => h X ^ 2) (gaussianMatrix p m) := by
  have hcont := gl_continuous_of_lip h L hLip
  have hF := gl_integrable_frobSq p m
  have hbound : ∀ X, |h X| ≤ |h 0| + L * frobNorm (Matrix.of X) := by
    intro X
    have h1 := hLip X 0
    have h2 : Matrix.of X - Matrix.of (0 : Fin p → Fin m → ℝ) = Matrix.of X := by
      ext i j; simp
    rw [h2] at h1
    have := abs_sub_abs_le_abs_sub (h X) (h 0)
    linarith
  have hsq : ∀ X : Fin p → Fin m → ℝ, frobNorm (Matrix.of X) ^ 2 = frobSq (Matrix.of X) := fun X =>
    Real.sq_sqrt (gl_frobSq_nonneg X)
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


lemma gl_mp_split (n N : ℕ) :
    MeasurePreserving
      (fun x : Fin (n + N) → ℝ => ((fun j : Fin n => x (Fin.castAdd N j)),
        (fun i : Fin N => x (Fin.natAdd n i))))
      (Measure.pi fun _ : Fin (n + N) => gaussianReal 0 1)
      ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := by
  have h1 := (measurePreserving_piCongrLeft (α := fun _ : Fin (n + N) => ℝ)
    (fun _ : Fin (n + N) => gaussianReal 0 1) finSumFinEquiv).symm
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin N => ℝ)
    (fun _ => gaussianReal 0 1)
  have h3 := h2.comp h1
  convert h3 using 1
  funext x
  simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft_symm_apply]

lemma gl_mp_row (n N : ℕ) :
    MeasurePreserving (fun H : Fin 1 → Fin (n + N) → ℝ => H 0) (gaussianMatrix 1 (n + N))
      (Measure.pi fun _ : Fin (n + N) => gaussianReal 0 1) :=
  measurePreserving_eval (fun _ : Fin 1 => Measure.pi fun _ : Fin (n + N) => gaussianReal 0 1) 0

lemma gl_integral_castAdd (n N : ℕ) (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) :
    ∫ H, f (fun j => H 0 (Fin.castAdd N j)) ∂(gaussianMatrix 1 (n + N))
      = ∫ x, f x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have h := (measurePreserving_fst (μ := Measure.pi fun _ : Fin n => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin N => gaussianReal 0 1)).comp ((gl_mp_split n N).comp (gl_mp_row n N))
  rw [← h.map_eq, integral_map h.measurable.aemeasurable hf.aestronglyMeasurable]
  rfl

lemma gl_integral_natAdd (n N : ℕ) (f : (Fin N → ℝ) → ℝ) (hf : Measurable f) :
    ∫ H, f (fun i => H 0 (Fin.natAdd n i)) ∂(gaussianMatrix 1 (n + N))
      = ∫ x, f x ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  have h := (measurePreserving_snd (μ := Measure.pi fun _ : Fin n => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin N => gaussianReal 0 1)).comp ((gl_mp_split n N).comp (gl_mp_row n N))
  rw [← h.map_eq, integral_map h.measurable.aemeasurable hf.aestronglyMeasurable]
  rfl


/-! ### New for the lower bound -/

lemma gl_integrable_iInf {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]
    [Nonempty ι] (f : ι → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) (hm : ∀ t, Measurable (f t)) :
    Integrable (fun ω => ⨅ t, f t ω) μ := by
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun t _ => (hf t).abs)
    (Measurable.iInf hm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_le]
  obtain ⟨t0⟩ := ‹Nonempty ι›
  have hb : BddBelow (Set.range fun t => f t ω) := (Set.finite_range _).bddBelow
  have hs : ∀ t, |f t ω| ≤ ∑ t, |f t ω| := fun t =>
    Finset.single_le_sum (f := fun t => |f t ω|) (fun t _ => abs_nonneg _) (Finset.mem_univ t)
  constructor
  · refine le_ciInf fun t => ?_
    have := neg_abs_le (f t ω)
    have := hs t
    linarith
  · have h1 := ciInf_le hb t0
    have h2 := hs t0
    have := le_abs_self (f t0 ω)
    linarith

lemma gl_norm_toLp {κ : Type*} [Fintype κ] (x : κ → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ κ)‖ = Real.sqrt (∑ i, x i ^ 2) := by
  rw [gl_norm_eq_sqrt]

open scoped Matrix.Norms.L2Operator RealInnerProductSpace in
/-- Net bound for the matrix process: `min_{u ∈ U} max_{v ∈ T} ⟨A u, v⟩ ≤ σ_min(A) + ε ‖A‖`
whenever `U` is an `ε`-net of the unit sphere of `ℝⁿ` and `T` consists of unit vectors. -/
lemma gl_matrix_side {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (ε : ℝ)
    (U : Finset (EuclideanSpace ℝ (Fin n))) (T : Finset (EuclideanSpace ℝ (Fin N)))
    (hT : ∀ v ∈ T, ‖v‖ = 1)
    (hcov : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 → ∃ u ∈ U, ‖x - u‖ ≤ ε)
    (hn : Nonempty {x : Fin n → ℝ // x ⬝ᵥ x = 1}) :
    ⨅ u : U, ⨆ v : T, ∑ i, ∑ j, v.1 i * A i j * u.1 j ≤ sMin A + ε * specNorm A := by
  set Φ := (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A with hΦ
  have hM : specNorm A = ‖Φ‖ := rfl
  have key : ∀ u : U, ⨆ v : T, ∑ i, ∑ j, v.1 i * A i j * u.1 j ≤ ‖Φ u.1‖ := by
    intro u
    refine Real.iSup_le (fun v => ?_) (norm_nonneg _)
    rw [← gl_inner_matrix]
    refine (real_inner_le_norm _ _).trans ?_
    rw [hT _ v.2, one_mul]
  set L := ⨅ u : U, ⨆ v : T, ∑ i, ∑ j, v.1 i * A i j * u.1 j with hL
  have hx : ∀ x : {x : Fin n → ℝ // x ⬝ᵥ x = 1},
      L - ε * specNorm A ≤ Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1)) := by
    intro x
    set xe : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x.1 with hxe
    have hxe1 : ‖xe‖ = 1 := by
      rw [hxe, gl_norm_toLp]
      have : ∑ i, x.1 i ^ 2 = 1 := by
        have h2 := x.2
        simp only [dotProduct] at h2
        simpa [sq] using h2
      rw [this, Real.sqrt_one]
    obtain ⟨u, hu, hxu⟩ := hcov xe hxe1
    have hb : BddBelow (Set.range fun u : U => ⨆ v : T, ∑ i, ∑ j, v.1 i * A i j * u.1 j) :=
      (Set.finite_range _).bddBelow
    have h1 : L ≤ ‖Φ u‖ := (ciInf_le hb ⟨u, hu⟩).trans (key ⟨u, hu⟩)
    have h2 : ‖Φ u‖ ≤ ‖Φ xe‖ + ‖Φ‖ * ε := by
      have hd : Φ u = Φ xe - Φ (xe - u) := by rw [map_sub]; abel
      rw [hd]
      refine (norm_sub_le _ _).trans (add_le_add_right ?_ _)
      exact (Φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left hxu (norm_nonneg _))
    have h3 : ‖Φ xe‖ = Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1)) := by
      have : Φ xe = WithLp.toLp 2 (A *ᵥ x.1) := rfl
      rw [this, gl_norm_toLp]
      simp [dotProduct, sq]
    rw [hM]
    linarith
  have := le_ciInf hx
  unfold sMin
  linarith

/-- The comparison process `⟨g, u⟩ + ⟨h, v⟩` written with one Gaussian row. -/
lemma gl_lin_append {N n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin N))
    (H : Fin 1 → Fin (n + N) → ℝ) :
    glLin (fun _ k => Fin.append (fun j => u j) (fun i => v i) k) H
      = ∑ j, u j * H 0 (Fin.castAdd N j) + ∑ i, v i * H 0 (Fin.natAdd n i) := by
  unfold glLin
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

open scoped RealInnerProductSpace in
/-- Net bound for the comparison process:
`min_{u ∈ U} max_{v ∈ T} (⟨g,u⟩ + ⟨h,v⟩) ≥ (1 - ε)‖h‖ - ‖g‖`. -/
lemma gl_gauss_side {N n : ℕ} (hN : 0 < N) (ε : ℝ)
    (U : Finset (EuclideanSpace ℝ (Fin n))) (T : Finset (EuclideanSpace ℝ (Fin N)))
    (hU : ∀ u ∈ U, ‖u‖ = 1) (hUne : Nonempty U)
    (hcov : ∀ y : EuclideanSpace ℝ (Fin N), ‖y‖ = 1 → ∃ v ∈ T, ‖y - v‖ ≤ ε)
    (H : Fin 1 → Fin (n + N) → ℝ) :
    (1 - ε) * Real.sqrt (∑ i, H 0 (Fin.natAdd n i) ^ 2)
        - Real.sqrt (∑ j, H 0 (Fin.castAdd N j) ^ 2)
      ≤ ⨅ u : U, ⨆ v : T, glLin (fun _ k => Fin.append (fun j => u.1 j) (fun i => v.1 i) k) H := by
  set h : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun i => H 0 (Fin.natAdd n i)) with hh
  have hhn : ‖h‖ = Real.sqrt (∑ i, H 0 (Fin.natAdd n i) ^ 2) := gl_norm_toLp _
  -- a unit vector aligned with `h`
  obtain ⟨y, hy1, hyh⟩ : ∃ y : EuclideanSpace ℝ (Fin N), ‖y‖ = 1 ∧ ⟪y, h⟫ = ‖h‖ := by
    by_cases h0 : h = 0
    · refine ⟨EuclideanSpace.single (⟨0, hN⟩ : Fin N) 1, by simp, ?_⟩
      rw [h0]; simp
    · refine ⟨(‖h‖⁻¹ : ℝ) • h, norm_smul_inv_norm h0, ?_⟩
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      have : ‖h‖ ≠ 0 := norm_ne_zero_iff.2 h0
      field_simp
  obtain ⟨v, hv, hyv⟩ := hcov y hy1
  have hvh : (1 - ε) * ‖h‖ ≤ ∑ i, v i * H 0 (Fin.natAdd n i) := by
    have e1 : ⟪v, h⟫ = ∑ i, v i * H 0 (Fin.natAdd n i) := by
      simp [hh, PiLp.inner_apply, mul_comm]
    have e2 : ⟪v, h⟫ = ⟪y, h⟫ - ⟪y - v, h⟫ := by rw [inner_sub_left]; ring
    have e3 : ⟪y - v, h⟫ ≤ ε * ‖h‖ :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hyv (norm_nonneg _))
    rw [← e1, e2, hyh]
    linarith
  refine le_ciInf fun u => ?_
  have hb : BddAbove (Set.range fun v : T =>
      glLin (fun _ k => Fin.append (fun j => u.1 j) (fun i => v.1 i) k) H) :=
    (Set.finite_range _).bddAbove
  refine le_trans ?_ (le_ciSup hb ⟨v, hv⟩)
  rw [gl_lin_append]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => u.1 j)
    (fun j => -H 0 (Fin.castAdd N j))
  rw [← gl_norm_eq_sqrt, hU _ u.2, one_mul] at hcs
  simp only [neg_sq, mul_neg, Finset.sum_neg_distrib] at hcs
  rw [← hhn]
  linarith

lemma gl_integrable_sqrt_sumsq {k m : ℕ} (σ : Fin k → Fin m) :
    Integrable (fun H : Fin 1 → Fin m → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2))
      (gaussianMatrix 1 m) := by
  have hQ : Integrable (fun H : Fin 1 → Fin m → ℝ => ∑ j, H 0 (σ j) ^ 2)
      (gaussianMatrix 1 m) :=
    integrable_finsetSum _ fun j _ => (gl_memLp_coord 0 (σ j) 2 (by simp)).integrable_sq
  refine Integrable.mono' ((integrable_const 1).add hQ) (by fun_prop : Continuous
    (fun H : Fin 1 → Fin m → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun H => ?_)
  have hQ0 : 0 ≤ ∑ j, H 0 (σ j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := Real.sq_sqrt hQ0
  have h2 := Real.sqrt_nonneg (∑ j, H 0 (σ j) ^ 2)
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (Real.sqrt (∑ j, H 0 (σ j) ^ 2) - 1)]

/-- Same-`u` increments of the matrix process: `‖u vᵀ - u v'ᵀ‖_F² = ‖v - v'‖²` for a unit `u`. -/
lemma gl_coeff_same {N n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (v v' : EuclideanSpace ℝ (Fin N))
    (hu : ‖u‖ = 1) :
    ∑ i, ∑ j, (v i * u j - v' i * u j) ^ 2 = ∑ i, (v i - v' i) ^ 2 := by
  have su : ∑ j, u j ^ 2 = 1 := by rw [← gl_norm_sq_eq, hu, one_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ∀ j, (v i * u j - v' i * u j) ^ 2 = (v i - v' i) ^ 2 * u j ^ 2 := fun j => by ring
  simp_rw [this]
  rw [← Finset.mul_sum, su, mul_one]

/-- The comparison bound at a fixed net scale `ε`:
`(1 - ε) 𝔼‖h_N‖ - 𝔼‖g_n‖ ≤ 𝔼 σ_min(G) + ε 𝔼‖G‖`. -/
lemma gl_scaled_bound {N n : ℕ} (hN : 0 < N) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    (1 - ε) * ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
        - ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      ≤ ∫ A, sMin (Matrix.of A) ∂(gaussianMatrix N n)
        + ε * ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) := by
  -- finite `ε`-nets of the two unit spheres
  obtain ⟨Fu, hFuS, hFufin, hFucov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).totallyBounded ε hε
  obtain ⟨Fv, hFvS, hFvfin, hFvcov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin N)) 1).totallyBounded ε hε
  set U := hFufin.toFinset with hUdef
  set T := hFvfin.toFinset with hTdef
  have hU1 : ∀ u ∈ U, ‖u‖ = 1 := by
    intro u hu
    rw [hUdef, Set.Finite.mem_toFinset] at hu
    simpa using hFuS hu
  have hT1 : ∀ v ∈ T, ‖v‖ = 1 := by
    intro v hv
    rw [hTdef, Set.Finite.mem_toFinset] at hv
    simpa using hFvS hv
  have hcovU : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 → ∃ u ∈ U, ‖x - u‖ ≤ ε := by
    intro x hx
    have hx' : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by simpa using hx
    obtain ⟨y, hy, hyx⟩ := Set.mem_iUnion₂.1 (hFucov hx')
    refine ⟨y, by rw [hUdef, Set.Finite.mem_toFinset]; exact hy, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hyx; exact hyx.le
  have hcovT : ∀ x : EuclideanSpace ℝ (Fin N), ‖x‖ = 1 → ∃ v ∈ T, ‖x - v‖ ≤ ε := by
    intro x hx
    have hx' : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 := by simpa using hx
    obtain ⟨y, hy, hyx⟩ := Set.mem_iUnion₂.1 (hFvcov hx')
    refine ⟨y, by rw [hTdef, Set.Finite.mem_toFinset]; exact hy, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hyx; exact hyx.le
  have hUne : Nonempty U := by
    obtain ⟨u, hu, -⟩ := hcovU (EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1) (by simp)
    exact ⟨⟨u, hu⟩⟩
  have hTne : Nonempty T := by
    obtain ⟨v, hv, -⟩ := hcovT (EuclideanSpace.single (⟨0, hN⟩ : Fin N) 1) (by simp)
    exact ⟨⟨v, hv⟩⟩
  have hsub : Nonempty {x : Fin n → ℝ // x ⬝ᵥ x = 1} :=
    ⟨⟨Pi.single (⟨0, hn⟩ : Fin n) 1, by simp [dotProduct, Pi.single_apply]⟩⟩
  -- the two Gaussian processes indexed by the nets
  set b : U → T → Fin 1 → Fin (n + N) → ℝ :=
    fun u v _ k => Fin.append (fun j => u.1 j) (fun i => v.1 i) k with hb
  set a : U → T → Fin N → Fin n → ℝ := fun u v i j => v.1 i * u.1 j with ha
  have hsame : ∀ (u : U) (t s : T),
      ∫ H, (glLin (b u t) H - glLin (b u s) H) ^ 2 ∂(gaussianMatrix 1 (n + N))
        ≤ ∫ G, (glLin (a u t) G - glLin (a u s) G) ^ 2 ∂(gaussianMatrix N n) := by
    intro u t s
    simp_rw [gl_lin_sub]
    rw [gl_integral_lin_sq, gl_integral_lin_sq]
    simp only [ha, hb, Pi.sub_apply]
    rw [gl_coeffY_sq, gl_coeff_same _ _ _ (hU1 _ u.2)]
    simp
  have hdiff : ∀ (u v : U) (t s : T), u ≠ v →
      ∫ G, (glLin (a u t) G - glLin (a v s) G) ^ 2 ∂(gaussianMatrix N n)
        ≤ ∫ H, (glLin (b u t) H - glLin (b v s) H) ^ 2 ∂(gaussianMatrix 1 (n + N)) := by
    intro u v t s _
    simp_rw [gl_lin_sub]
    rw [gl_integral_lin_sq, gl_integral_lin_sq]
    simp only [ha, hb, Pi.sub_apply]
    rw [gl_coeffY_sq]
    exact gl_coeff_ineq _ _ _ _ (hU1 _ u.2) (hU1 _ v.2) (hT1 _ t.2) (hT1 _ s.2)
  have hGM := gordon_minimax (fun u t H => glLin (b u t) H) (fun u t G => glLin (a u t) G)
    (gl_hasGaussianLaw_lin (fun p : U × T => b p.1 p.2))
    (gl_hasGaussianLaw_lin (fun p : U × T => a p.1 p.2))
    (fun u t => gl_integral_lin _) (fun u t => gl_integral_lin _) hsame hdiff
  -- integrability
  have hsMin : Integrable (fun A : Fin N → Fin n → ℝ => sMin (Matrix.of A))
      (gaussianMatrix N n) :=
    (gl_integrable_of_lip (fun A : Fin N → Fin n → ℝ => sMin (Matrix.of A)) 1 zero_le_one
      fun X Y => by rw [one_mul]; exact sMin_lipschitz (Matrix.of X) (Matrix.of Y)).1
  have hspec : Integrable (fun A : Fin N → Fin n → ℝ => specNorm (Matrix.of A))
      (gaussianMatrix N n) :=
    (gl_integrable_of_lip (fun A : Fin N → Fin n → ℝ => specNorm (Matrix.of A)) 1 zero_le_one
      fun X Y => by rw [one_mul]; exact specNorm_lipschitz (Matrix.of X) (Matrix.of Y)).1
  have hXmm : Integrable (fun H => ⨅ u : U, ⨆ t : T, glLin (b u t) H)
      (gaussianMatrix 1 (n + N)) :=
    gl_integrable_iInf (fun u H => ⨆ t : T, glLin (b u t) H)
      (fun u => gl_integrable_iSup (fun t H => glLin (b u t) H) (fun t => gl_integrable_lin _)
        (fun t => (gl_continuous_lin _).measurable))
      (fun u => Measurable.iSup fun t => (gl_continuous_lin _).measurable)
  have hYmm : Integrable (fun G => ⨅ u : U, ⨆ t : T, glLin (a u t) G)
      (gaussianMatrix N n) :=
    gl_integrable_iInf (fun u G => ⨆ t : T, glLin (a u t) G)
      (fun u => gl_integrable_iSup (fun t G => glLin (a u t) G) (fun t => gl_integrable_lin _)
        (fun t => (gl_continuous_lin _).measurable))
      (fun u => Measurable.iSup fun t => (gl_continuous_lin _).measurable)
  have hg := gl_integrable_sqrt_sumsq (m := n + N) (fun j : Fin n => Fin.castAdd N j)
  have hh := gl_integrable_sqrt_sumsq (m := n + N) (fun i : Fin N => Fin.natAdd n i)
  have hEN := gl_integral_natAdd n N (fun x => Real.sqrt (∑ i, x i ^ 2)) (by fun_prop)
  have hEn := gl_integral_castAdd n N (fun x => Real.sqrt (∑ j, x j ^ 2)) (by fun_prop)
  -- chain of inequalities
  calc (1 - ε) * ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
        - ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      = ∫ H, ((1 - ε) * Real.sqrt (∑ i, H 0 (Fin.natAdd n i) ^ 2)
          - Real.sqrt (∑ j, H 0 (Fin.castAdd N j) ^ 2)) ∂(gaussianMatrix 1 (n + N)) := by
        rw [integral_sub (hh.const_mul _) hg, integral_const_mul]
        simp only at hEN hEn
        rw [hEN, hEn]
    _ ≤ ∫ H, (⨅ u : U, ⨆ t : T, glLin (b u t) H) ∂(gaussianMatrix 1 (n + N)) := by
        refine integral_mono ((hh.const_mul _).sub hg) hXmm fun H => ?_
        exact gl_gauss_side hN ε U T hU1 hUne hcovT H
    _ ≤ ∫ G, (⨅ u : U, ⨆ t : T, glLin (a u t) G) ∂(gaussianMatrix N n) := hGM
    _ ≤ ∫ A, (sMin (Matrix.of A) + ε * specNorm (Matrix.of A)) ∂(gaussianMatrix N n) := by
        refine integral_mono hYmm (hsMin.add (hspec.const_mul ε)) fun G => ?_
        refine le_trans (le_of_eq ?_) (gl_matrix_side (Matrix.of G) ε U T hT1 hcovU hsub)
        congr 1; funext u; congr 1; funext t
        simp only [glLin, ha, Matrix.of_apply]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∫ A, sMin (Matrix.of A) ∂(gaussianMatrix N n)
          + ε * ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) := by
        rw [integral_add hsMin (hspec.const_mul ε), integral_const_mul]

open scoped Matrix.Norms.L2Operator in
lemma gl_specNorm_nonneg {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) : 0 ≤ specNorm A :=
  norm_nonneg _

end GaussianMatrix

open GaussianMatrix

theorem solution {N n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt N - Real.sqrt n ≤ ∫ A, sMin (Matrix.of A) ∂(gaussianMatrix N n) := by
  have hpos : 0 ≤ ∫ A, sMin (Matrix.of A) ∂(gaussianMatrix N n) :=
    integral_nonneg fun A => Real.iInf_nonneg fun _ => Real.sqrt_nonneg _
  rcases le_or_gt N n with hNn | hNn
  · have : Real.sqrt N ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hNn)
    linarith
  have hN : 0 < N := lt_of_lt_of_le (by omega) hNn
  set EN := ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
    with hENdef
  set En := ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
    with hEndef
  set E := ∫ A, sMin (Matrix.of A) ∂(gaussianMatrix N n) with hE
  set Sp := ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) with hSp
  have hD : Real.sqrt N - Real.sqrt n ≤ EN - En :=
    expectation_norm_gaussian_diff hn hNn.le
  have hEN0 : 0 ≤ EN := integral_nonneg fun _ => Real.sqrt_nonneg _
  have hSp0 : 0 ≤ Sp := integral_nonneg fun A => gl_specNorm_nonneg (Matrix.of A)
  have key : ∀ ε : ℝ, 0 < ε → EN - En - ε * (EN + Sp) ≤ E := by
    intro ε hε
    have := gl_scaled_bound (N := N) (n := n) hN (by omega) ε hε
    linarith
  -- let `ε → 0`
  have hlim : EN - En ≤ E := by
    by_contra hcon
    push Not at hcon
    set δ := EN - En - E with hδ
    have hδ0 : 0 < δ := by linarith
    set C := EN + Sp + 1 with hC
    have hC0 : 0 < C := by linarith
    have h1 := key (δ / (2 * C)) (by positivity)
    have h2 : δ / (2 * C) * (EN + Sp) ≤ δ / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  linarith
