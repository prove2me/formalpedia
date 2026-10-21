-- Prove2me | solution 1 for DynSampleSize.Stoch.eq_4_26
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:22:49.708716+00:00
-- url     : https://prove2.me/submissions/21c293b4-d1b8-475b-850c-e97e35e6ce3c

import Mathlib
import Definitions.Def_DynSampleSize_Stoch_UniformConvexity
import Definitions.Def_DynSampleSize_Stoch_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory DynSampleSize.Stoch



lemma dss_oneD (φ g h : ℝ → ℝ) (c : ℝ) (hφ : ∀ t, HasDerivAt φ (g t) t)
    (hg : ∀ t, HasDerivAt g (h t) t) (hh : ∀ t, h t ≤ c) : φ 1 ≤ φ 0 + g 0 + c / 2 := by
  have hgt : ∀ t, 0 ≤ t → g t ≤ g 0 + c * t := by
    intro t ht
    have hF : ∀ x, HasDerivAt (fun x => g x - c * x) (h x - c) x := fun x =>
      ((hg x).sub ((hasDerivAt_id' x).const_mul c)).congr_deriv (by ring)
    have hanti : Antitone (fun x => g x - c * x) :=
      antitone_of_deriv_nonpos (fun x => (hF x).differentiableAt) (fun x => by
        rw [(hF x).deriv]; linarith [hh x])
    have := hanti ht
    simp only [mul_zero, sub_zero] at this
    linarith
  have hF : ∀ x, HasDerivAt (fun x => φ x - g 0 * x - c / 2 * x ^ 2) (g x - g 0 - c * x) x := by
    intro x
    have h1 := (hφ x).sub ((hasDerivAt_id' x).const_mul (g 0))
    have h2 := ((hasDerivAt_pow 2 x).const_mul (c / 2))
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    norm_num <;> ring
  have hanti : AntitoneOn (fun x => φ x - g 0 * x - c / 2 * x ^ 2) (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun x _ => (hF x).continuousAt.continuousWithinAt
    · exact fun x _ => (hF x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hF x).deriv]
      linarith [hgt x hx.1.le]
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [mul_zero, sub_zero, zero_pow two_ne_zero, mul_one, one_pow] at this
  linarith

lemma dss_quad {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : UniformlyConvex J lam L) (w d : EuclideanSpace ℝ (Fin m)) :
    J w + inner ℝ (gradient J w) d + lam / 2 * ‖d‖ ^ 2 ≤ J (w + d) ∧
      J (w + d) ≤ J w + inner ℝ (gradient J w) d + L / 2 * ‖d‖ ^ 2 := by
  obtain ⟨hC, -, -, hH⟩ := hJ
  have hdiff : Differentiable ℝ J := hC.differentiable (by norm_num)
  have hdiff2 : Differentiable ℝ (fderiv ℝ J) :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  set γ : ℝ → EuclideanSpace ℝ (Fin m) := fun t => w + t • d with hγ
  have hγd : ∀ t, HasDerivAt γ d t := fun t => by
    simpa [hγ] using ((hasDerivAt_id' t).smul_const d).const_add w
  have h1 : ∀ t, HasDerivAt (fun t => J (γ t)) (fderiv ℝ J (γ t) d) t := fun t =>
    (hdiff (γ t)).hasFDerivAt.comp_hasDerivAt t (hγd t)
  have h2 : ∀ t, HasDerivAt (fun t => fderiv ℝ J (γ t) d)
      (fderiv ℝ (fderiv ℝ J) (γ t) d d) t := fun t => by
    have := (hdiff2 (γ t)).hasFDerivAt.comp_hasDerivAt t (hγd t)
    exact (ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt.comp_hasDerivAt t this
  have hgrad : fderiv ℝ J w d = inner ℝ (gradient J w) d := by
    unfold gradient
    rw [InnerProductSpace.toDual_symm_apply]
  have e0 : γ 0 = w := by simp [hγ]
  have e1 : γ 1 = w + d := by simp [hγ]
  constructor
  · have := dss_oneD (fun t => -J (γ t)) (fun t => -fderiv ℝ J (γ t) d)
      (fun t => -fderiv ℝ (fderiv ℝ J) (γ t) d d) (-(lam * ‖d‖ ^ 2))
      (fun t => (h1 t).neg) (fun t => (h2 t).neg) (fun t => by linarith [(hH (γ t) d).1])
    simp only [e0, e1, hgrad] at this
    linarith
  · have := dss_oneD (fun t => J (γ t)) (fun t => fderiv ℝ J (γ t) d)
      (fun t => fderiv ℝ (fderiv ℝ J) (γ t) d d) (L * ‖d‖ ^ 2)
      h1 h2 (fun t => (hH (γ t) d).2)
    simp only [e0, e1, hgrad] at this
    linarith

lemma dss_taylor {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : UniformlyConvex J lam L) (w g : EuclideanSpace ℝ (Fin m)) :
    J (w - (1 / L) • g) ≤ J w - (1 / L) * inner ℝ (gradient J w) g + 1 / (2 * L) * ‖g‖ ^ 2 := by
  have hL : 0 < L := hJ.2.1.trans hJ.2.2.1
  have := (dss_quad J lam L hJ w ((-(1 / L)) • g)).2
  have e : w + (-(1 / L)) • g = w - (1 / L) • g := by rw [neg_smul, sub_eq_add_neg]
  rw [e, inner_smul_right, norm_smul, mul_pow] at this
  have h2 : ‖-(1 / L)‖ ^ 2 = (1 / L) ^ 2 := by
    rw [norm_neg, Real.norm_of_nonneg (by positivity)]
  rw [h2] at this
  have h3 : L / 2 * ((1 / L) ^ 2 * ‖g‖ ^ 2) = 1 / (2 * L) * ‖g‖ ^ 2 := by
    field_simp
  rw [h3] at this
  linarith

lemma dss_lower {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : UniformlyConvex J lam L) (w g : EuclideanSpace ℝ (Fin m)) :
    J w - (1 / L) * (‖gradient J w‖ * ‖g‖) ≤ J (w - (1 / L) • g) := by
  have hL : 0 < L := hJ.2.1.trans hJ.2.2.1
  have hlam : 0 < lam := hJ.2.1
  have := (dss_quad J lam L hJ w ((-(1 / L)) • g)).1
  have e : w + (-(1 / L)) • g = w - (1 / L) • g := by rw [neg_smul, sub_eq_add_neg]
  rw [e, inner_smul_right] at this
  have h1 : inner ℝ (gradient J w) g ≤ ‖gradient J w‖ * ‖g‖ := by
    have := abs_real_inner_le_norm (gradient J w) g
    linarith [le_abs_self (inner ℝ (gradient J w) g)]
  have h2 : 0 ≤ lam / 2 * ‖(-(1 / L)) • g‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 / L by positivity)]


lemma dss_gd {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : UniformlyConvex J lam L) (wstar : EuclideanSpace ℝ (Fin m))
    (hwstar : ∀ w, J wstar ≤ J w) (w : EuclideanSpace ℝ (Fin m)) :
    lam * (J w - J wstar) ≤ inner ℝ (gradient J w) (gradient J w) := by
  have hlam : 0 < lam := hJ.2.1
  have h := (dss_quad J lam L hJ w (wstar - w)).1
  rw [add_sub_cancel] at h
  have h1 := hwstar w
  have h2 : -(‖gradient J w‖ * ‖wstar - w‖) ≤ inner ℝ (gradient J w) (wstar - w) := by
    have := abs_real_inner_le_norm (gradient J w) (wstar - w)
    linarith [neg_abs_le (inner ℝ (gradient J w) (wstar - w))]
  rw [real_inner_self_eq_norm_sq]
  set G := ‖gradient J w‖
  set r := ‖wstar - w‖
  have h3 : J w - J wstar ≤ G * r - lam / 2 * r ^ 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hlam.le, sq_nonneg (G - lam * r), sq_nonneg G]




section meas

variable {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]

lemma dss_memLp_batch (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) (hgrad : MemLp (gradℓ w) 2 P) (n : ℕ) :
    MemLp (batchGrad gradℓ n w) 2 (Measure.pi (fun _ : Fin n => P)) := by
  unfold batchGrad
  have h : ∀ i : Fin n, MemLp (fun b : Fin n → Z => gradℓ w (b i)) 2
      (Measure.pi (fun _ : Fin n => P)) := fun i =>
    hgrad.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => P) i)
  have hs := memLp_finsetSum' (s := Finset.univ) (fun i _ => h i)
  have e : (fun b : Fin n → Z => (1 / (n : ℝ)) • ∑ i, gradℓ w (b i)) =
      (1 / (n : ℝ)) • ∑ i : Fin n, fun b : Fin n → Z => gradℓ w (b i) := by
    ext b
    simp
  rw [e]
  exact hs.const_smul _

lemma dss_integral_eval (f : Z → EuclideanSpace ℝ (Fin m)) (hf : AEStronglyMeasurable f P)
    (n : ℕ) (i : Fin n) :
    ∫ b : Fin n → Z, f (b i) ∂(Measure.pi (fun _ : Fin n => P)) = ∫ z, f z ∂P := by
  have hmp := measurePreserving_eval (fun _ : Fin n => P) i
  have h := integral_map (μ := Measure.pi (fun _ : Fin n => P)) (φ := Function.eval i)
    (measurable_pi_apply i).aemeasurable (f := f) (by rw [hmp.map_eq]; exact hf)
  rw [hmp.map_eq] at h
  exact h.symm

lemma dss_integral_batch (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) (hgrad : MemLp (gradℓ w) 2 P) (n : ℕ) (hn : 1 ≤ n) :
    ∫ b, batchGrad gradℓ n w b ∂(Measure.pi (fun _ : Fin n => P)) = ∫ z, gradℓ w z ∂P := by
  unfold batchGrad
  rw [integral_smul, integral_finsetSum]
  · have h : ∀ i : Fin n, ∫ b : Fin n → Z, gradℓ w (b i) ∂(Measure.pi (fun _ : Fin n => P)) =
        ∫ z, gradℓ w z ∂P := fun i => dss_integral_eval P (gradℓ w) hgrad.1 n i
    simp only [h]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul, one_div, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (by omega)), one_smul]
  · intro i _
    exact (hgrad.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => P) i)).integrable one_le_two

end meas

lemma dss_sq_decomp {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → EuclideanSpace ℝ (Fin m)) (hY : MemLp Y 2 μ) :
    ∫ x, ‖Y x‖ ^ 2 ∂μ = ‖∫ x, Y x ∂μ‖ ^ 2 + ∫ x, ‖Y x - ∫ y, Y y ∂μ‖ ^ 2 ∂μ := by
  set c := ∫ x, Y x ∂μ with hc
  have hint : Integrable Y μ := hY.integrable one_le_two
  have hsq : Integrable (fun x => ‖Y x‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm hY.1).1 hY)
  have hYc : MemLp (fun x => Y x - c) 2 μ := hY.sub (memLp_const c)
  have hsq2 : Integrable (fun x => ‖Y x - c‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm hYc.1).1 hYc)
  have hinner : Integrable (fun x => inner ℝ c (Y x - c)) μ :=
    (hint.sub (integrable_const c)).const_inner c
  have hpt : ∀ x, ‖Y x‖ ^ 2 = ‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c) + ‖Y x - c‖ ^ 2 := by
    intro x
    have := norm_add_sq_real c (Y x - c)
    simpa using this
  have hsub : Integrable (fun x => Y x - c) μ := hint.sub (integrable_const c)
  have h0 : ∫ x, inner ℝ c (Y x - c) ∂μ = 0 := by
    have := integral_inner (𝕜 := ℝ) hsub c
    rw [this, integral_sub hint (integrable_const c)]
    simp [hc]
  have e1 : Integrable (fun x => ‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c)) μ :=
    (integrable_const _).add (hinner.const_mul 2)
  have i1 : ∫ x, (‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c) + ‖Y x - c‖ ^ 2) ∂μ =
      (∫ x, (‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c)) ∂μ) + ∫ x, ‖Y x - c‖ ^ 2 ∂μ :=
    integral_add e1 hsq2
  have i2 : ∫ x, (‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c)) ∂μ =
      (∫ x, ‖c‖ ^ 2 ∂μ) + ∫ x, 2 * inner ℝ c (Y x - c) ∂μ :=
    integral_add (integrable_const _) (hinner.const_mul 2)
  have i3 : ∫ x, 2 * inner ℝ c (Y x - c) ∂μ = 2 * ∫ x, inner ℝ c (Y x - c) ∂μ :=
    integral_const_mul 2 _
  calc ∫ x, ‖Y x‖ ^ 2 ∂μ
      = ∫ x, (‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c) + ‖Y x - c‖ ^ 2) ∂μ := by
        congr 1; ext x; exact hpt x
    _ = ‖c‖ ^ 2 + ∫ x, ‖Y x - c‖ ^ 2 ∂μ := by
        rw [i1, i2, i3, h0]
        simp

lemma dss_vecVar_eq {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → EuclideanSpace ℝ (Fin m)) (hY : MemLp Y 2 μ) :
    vecVar μ Y = ∑ k, variance (fun x => Y x k) μ := by
  have hk : ∀ k, MemLp (fun x => Y x k) 2 μ := fun k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).comp_memLp' hY
  have hmean : ∀ k, (∫ x, Y x ∂μ) k = ∫ x, Y x k ∂μ := fun k => by
    have := (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).integral_comp_comm
      (hY.integrable one_le_two)
    simpa using this.symm
  unfold vecVar
  have e : ∀ x, ‖Y x - ∫ y, Y y ∂μ‖ ^ 2 = ∑ k, (Y x k - ∫ y, Y y k ∂μ) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, hmean k]
  simp_rw [e]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [variance_eq_integral (hk k).aemeasurable]
  · intro k _
    exact ((hk k).sub (memLp_const _)).integrable_sq

lemma dss_smv {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) (hgrad : MemLp (gradℓ w) 2 P) (n : ℕ) (hn : 1 ≤ n) :
    vecVar (Measure.pi (fun _ : Fin n => P)) (batchGrad gradℓ n w) =
      vecVar P (gradℓ w) / n := by
  rw [dss_vecVar_eq _ _ (dss_memLp_batch P gradℓ w hgrad n), dss_vecVar_eq P _ hgrad,
    Finset.sum_div]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hX : MemLp (fun z => gradℓ w z k) 2 P :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).comp_memLp' hgrad
  have e : (fun b : Fin n → Z => batchGrad gradℓ n w b k) =
      (1 / (n : ℝ)) • ∑ i : Fin n, fun b : Fin n → Z => gradℓ w (b i) k := by
    ext b
    simp [batchGrad, Finset.sum_apply]
  rw [e, variance_smul, variance_sum_pi (X := fun _ : Fin n => fun z => gradℓ w z k)
    (fun _ => hX)]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp


lemma dss_step {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin m) → Z → ℝ)
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (hmodel : StochModel P ℓ gradℓ) (lam L : ℝ) (hJ : UniformlyConvex (objective P ℓ) lam L)
    (w : EuclideanSpace ℝ (Fin m)) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun b => objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b))
        (Measure.pi (fun _ : Fin n => P)) ∧
      Integrable (fun b => ‖batchGrad gradℓ n w b‖ ^ 2) (Measure.pi (fun _ : Fin n => P)) ∧
      ∫ b, objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b) ∂(Measure.pi (fun _ : Fin n => P)) ≤
        objective P ℓ w - 1 / L * ‖gradient (objective P ℓ) w‖ ^ 2 +
          1 / (2 * L) * ∫ b, ‖batchGrad gradℓ n w b‖ ^ 2 ∂(Measure.pi (fun _ : Fin n => P)) ∧
      ∫ b, ‖batchGrad gradℓ n w b‖ ^ 2 ∂(Measure.pi (fun _ : Fin n => P)) =
        ‖gradient (objective P ℓ) w‖ ^ 2 +
          vecVar (Measure.pi (fun _ : Fin n => P)) (batchGrad gradℓ n w) := by
  set J := objective P ℓ with hJdef
  set μ := Measure.pi (fun _ : Fin n => P) with hμ
  set g := batchGrad gradℓ n w with hg
  have hL : 0 < L := hJ.2.1.trans hJ.2.2.1
  have hg2 : MemLp g 2 μ := dss_memLp_batch P gradℓ w (hmodel.memLp_grad w) n
  have hg1 : Integrable g μ := hg2.integrable one_le_two
  have hsq : Integrable (fun b => ‖g b‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm hg2.1).1 hg2)
  have hnorm : Integrable (fun b => ‖g b‖) μ := hg1.norm
  have hmean : ∫ b, g b ∂μ = gradient J w := by
    rw [hg, hμ, dss_integral_batch P gradℓ w (hmodel.memLp_grad w) n hn]
    exact ((hmodel.hasGradientAt_objective w).gradient).symm
  have hdecomp := dss_sq_decomp μ g hg2
  have hFm : AEStronglyMeasurable (fun b => J (w - (1 / L) • g b)) μ :=
    hJ.1.continuous.comp_aestronglyMeasurable
      (aestronglyMeasurable_const.sub (hg2.1.const_smul (1 / L)))
  have hF : Integrable (fun b => J (w - (1 / L) • g b)) μ := by
    have hB : Integrable (fun b => (1 / L) * (‖gradient J w‖ * ‖g b‖) +
        1 / (2 * L) * ‖g b‖ ^ 2) μ :=
      (hnorm.const_mul (‖gradient J w‖)).const_mul (1 / L) |>.add (hsq.const_mul _)
    have hd : Integrable (fun b => J (w - (1 / L) • g b) - J w) μ := by
      refine Integrable.mono' hB (hFm.sub aestronglyMeasurable_const) ?_
      refine Filter.Eventually.of_forall (fun b => ?_)
      have h1 := dss_taylor J lam L hJ w (g b)
      have h2 := dss_lower J lam L hJ w (g b)
      have h3 : inner ℝ (gradient J w) (g b) ≥ -(‖gradient J w‖ * ‖g b‖) := by
        have := abs_real_inner_le_norm (gradient J w) (g b)
        linarith [neg_abs_le (inner ℝ (gradient J w) (g b))]
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · nlinarith [mul_nonneg (show 0 ≤ 1 / L by positivity) (mul_nonneg (norm_nonneg (gradient J w)) (norm_nonneg (g b))), sq_nonneg ‖g b‖,
          show 0 ≤ 1 / (2 * L) by positivity]
      · have h4 : (1 / L) * inner ℝ (gradient J w) (g b) ≥ -((1 / L) * (‖gradient J w‖ * ‖g b‖)) := by
          nlinarith [mul_le_mul_of_nonneg_left h3 (show 0 ≤ 1 / L by positivity)]
        linarith
    refine (hd.add (integrable_const (J w))).congr (Filter.Eventually.of_forall (fun b => ?_))
    simp
  refine ⟨hF, hsq, ?_, ?_⟩
  · have hR : Integrable (fun b => J w - (1 / L) * inner ℝ (gradient J w) (g b) +
        1 / (2 * L) * ‖g b‖ ^ 2) μ :=
      ((integrable_const _).sub ((hg1.const_inner (gradient J w)).const_mul (1 / L))).add
        (hsq.const_mul _)
    have hle := integral_mono hF hR (fun b => dss_taylor J lam L hJ w (g b))
    refine hle.trans (le_of_eq ?_)
    have eA : Integrable (fun b => J w - 1 / L * inner ℝ (gradient J w) (g b)) μ :=
      (integrable_const _).sub ((hg1.const_inner (gradient J w)).const_mul (1 / L))
    have i1 : ∫ b, (J w - 1 / L * inner ℝ (gradient J w) (g b) + 1 / (2 * L) * ‖g b‖ ^ 2) ∂μ =
        (∫ b, (J w - 1 / L * inner ℝ (gradient J w) (g b)) ∂μ) +
          ∫ b, 1 / (2 * L) * ‖g b‖ ^ 2 ∂μ := integral_add eA (hsq.const_mul _)
    have i2 : ∫ b, (J w - 1 / L * inner ℝ (gradient J w) (g b)) ∂μ =
        (∫ b, J w ∂μ) - ∫ b, 1 / L * inner ℝ (gradient J w) (g b) ∂μ :=
      integral_sub (integrable_const _) ((hg1.const_inner (gradient J w)).const_mul (1 / L))
    have i3 : ∫ b, 1 / L * inner ℝ (gradient J w) (g b) ∂μ =
        1 / L * ∫ b, inner ℝ (gradient J w) (g b) ∂μ := integral_const_mul _ _
    have i4 : ∫ b, inner ℝ (gradient J w) (g b) ∂μ = inner ℝ (gradient J w) (∫ b, g b ∂μ) :=
      integral_inner hg1 _
    have i5 : ∫ b, 1 / (2 * L) * ‖g b‖ ^ 2 ∂μ = 1 / (2 * L) * ∫ b, ‖g b‖ ^ 2 ∂μ :=
      integral_const_mul _ _
    rw [i1, i2, i3, i4, i5, hmean]
    simp [real_inner_self_eq_norm_sq]
  · have hv : vecVar μ g = ∫ x, ‖g x - ∫ y, g y ∂μ‖ ^ 2 ∂μ := rfl
    rw [hv, hdecomp, hmean]


lemma dss_426 {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin m) → Z → ℝ)
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (hmodel : StochModel P ℓ gradℓ) (lam L : ℝ) (hJ : UniformlyConvex (objective P ℓ) lam L)
    (w : EuclideanSpace ℝ (Fin m)) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun b => objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b))
        (Measure.pi (fun _ : Fin n => P)) ∧
      ∫ b, objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b) ∂(Measure.pi (fun _ : Fin n => P)) ≤
        objective P ℓ w - 1 / (2 * L) * ‖gradient (objective P ℓ) w‖ ^ 2 +
          1 / (2 * L * n) * vecVar P (gradℓ w) := by
  obtain ⟨hF, hsq, h3, h4⟩ := dss_step P ℓ gradℓ hmodel lam L hJ w n hn
  refine ⟨hF, ?_⟩
  have hL : 0 < L := hJ.2.1.trans hJ.2.2.1
  have hv := dss_smv P gradℓ w (hmodel.memLp_grad w) n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [h4] at h3
  have h5 : 1 / (2 * L) * vecVar (Measure.pi (fun _ : Fin n => P)) (batchGrad gradℓ n w) ≤
      1 / (2 * L * n) * vecVar P (gradℓ w) := by
    have e : 1 / (2 * L * n) * vecVar P (gradℓ w) = 1 / (2 * L) * (vecVar P (gradℓ w) / n) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hv.le (by positivity)
  have e2 : 1 / L * ‖gradient (objective P ℓ) w‖ ^ 2 =
      2 * (1 / (2 * L) * ‖gradient (objective P ℓ) w‖ ^ 2) := by
    field_simp
  nlinarith [h3, h5, e2]

theorem solution {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin m) → Z → ℝ)
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (hmodel : StochModel P ℓ gradℓ) (lam L : ℝ) (hJ : UniformlyConvex (objective P ℓ) lam L)
    (w : EuclideanSpace ℝ (Fin m)) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun b => objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b))
        (Measure.pi (fun _ : Fin n => P)) ∧
      ∫ b, objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b) ∂(Measure.pi (fun _ : Fin n => P)) ≤
        objective P ℓ w - 1 / (2 * L) * ‖gradient (objective P ℓ) w‖ ^ 2 +
          1 / (2 * L * n) * vecVar P (gradℓ w) :=
  dss_426 P ℓ gradℓ hmodel lam L hJ w n hn
