-- Prove2me | solution 1 for BoltzmannBGK.maxwellian_integral
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:36:42.822126+00:00
-- url     : https://prove2.me/submissions/d3985ba4-91a7-4d04-83c0-173d6297282b

import Definitions.Def_BoltzmannBGK_model
import Definitions.Def_BoltzmannBGK_slab

open MeasureTheory Real
open BoltzmannBGK

/-! ## One-dimensional Gaussian integrals -/

theorem W3a_BoltzmannBGK_intPow (c θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    Integrable (fun x : ℝ => (x - c) ^ n * exp (-((x - c) ^ 2 / (2 * θ)))) := by
  have hb : 0 < 1 / (2 * θ) := by positivity
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb (s := (n : ℝ))
    (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)).comp_sub_right c
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Real.rpow_natCast]
  congr 2
  ring

theorem W3a_BoltzmannBGK_intExp (c θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun x : ℝ => exp (-((x - c) ^ 2 / (2 * θ)))) := by
  simpa using W3a_BoltzmannBGK_intPow c θ hθ 0

theorem W3a_BoltzmannBGK_intLin (c θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun x : ℝ => x * exp (-((x - c) ^ 2 / (2 * θ)))) := by
  refine ((W3a_BoltzmannBGK_intPow c θ hθ 1).add
    ((W3a_BoltzmannBGK_intExp c θ hθ).const_mul c)).congr (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply]
  ring

theorem W3a_BoltzmannBGK_intSq (c θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun x : ℝ => x ^ 2 * exp (-((x - c) ^ 2 / (2 * θ)))) := by
  refine (((W3a_BoltzmannBGK_intPow c θ hθ 2).add
    ((W3a_BoltzmannBGK_intPow c θ hθ 1).const_mul (2 * c))).add
    ((W3a_BoltzmannBGK_intExp c θ hθ).const_mul (c ^ 2))).congr (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply]
  ring

theorem W3a_BoltzmannBGK_I0 (c θ : ℝ) (hθ : 0 < θ) :
    ∫ x : ℝ, exp (-((x - c) ^ 2 / (2 * θ))) = sqrt (2 * π * θ) := by
  have h1 := integral_sub_right_eq_self (μ := volume)
    (fun x : ℝ => exp (-(x ^ 2 / (2 * θ)))) c
  rw [h1]
  have h2 : (fun x : ℝ => exp (-(x ^ 2 / (2 * θ)))) = fun x => exp (-(1 / (2 * θ)) * x ^ 2) := by
    funext x; congr 1; ring
  rw [h2, integral_gaussian]
  congr 1
  rw [div_div_eq_mul_div, div_one]
  ring

theorem W3a_BoltzmannBGK_odd (g : ℝ → ℝ) (hg : ∀ x, g (-x) = -g x) : ∫ x, g x = 0 := by
  have h := integral_neg_eq_self g (volume : Measure ℝ)
  simp only [hg, integral_neg] at h
  linarith

theorem W3a_BoltzmannBGK_Iodd (c θ : ℝ) (n : ℕ) (hn : Odd n) :
    ∫ x : ℝ, (x - c) ^ n * exp (-((x - c) ^ 2 / (2 * θ))) = 0 := by
  have h1 := integral_sub_right_eq_self (μ := volume)
    (fun x : ℝ => x ^ n * exp (-(x ^ 2 / (2 * θ)))) c
  rw [h1]
  apply W3a_BoltzmannBGK_odd
  intro x
  rw [hn.neg_pow, neg_sq]
  ring

theorem W3a_BoltzmannBGK_I2 (c θ : ℝ) (hθ : 0 < θ) :
    ∫ x : ℝ, (x - c) ^ 2 * exp (-((x - c) ^ 2 / (2 * θ))) = θ * sqrt (2 * π * θ) := by
  obtain ⟨v, rfl⟩ : ∃ v : NNReal, (v : ℝ) = θ := ⟨⟨θ, hθ.le⟩, rfl⟩
  have hv : v ≠ 0 := by rintro rfl; simp at hθ
  have h1 := ProbabilityTheory.variance_fun_id_gaussianReal (μ := c) (v := v)
  rw [ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable] at h1
  simp only [ProbabilityTheory.integral_id_gaussianReal] at h1
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv] at h1
  have hs : 0 < sqrt (2 * π * (v : ℝ)) := by positivity
  have hss : sqrt (2 * π * (v : ℝ)) * (sqrt (2 * π * (v : ℝ)))⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  calc ∫ x : ℝ, (x - c) ^ 2 * exp (-((x - c) ^ 2 / (2 * (v : ℝ))))
      = ∫ x : ℝ, sqrt (2 * π * (v : ℝ)) *
          (ProbabilityTheory.gaussianPDFReal c v x • (x - c) ^ 2) := by
        congr 1; funext x
        simp only [ProbabilityTheory.gaussianPDFReal, smul_eq_mul]
        rw [neg_div]
        linear_combination (-(exp (-((x - c) ^ 2 / (2 * (v : ℝ)))) * (x - c) ^ 2)) * hss
    _ = (v : ℝ) * sqrt (2 * π * (v : ℝ)) := by
        rw [integral_const_mul, h1]; ring

theorem W3a_BoltzmannBGK_I1lin (c θ : ℝ) (hθ : 0 < θ) :
    ∫ x : ℝ, x * exp (-((x - c) ^ 2 / (2 * θ))) = c * sqrt (2 * π * θ) := by
  have e : (fun x : ℝ => x * exp (-((x - c) ^ 2 / (2 * θ)))) =
      fun x => (x - c) ^ 1 * exp (-((x - c) ^ 2 / (2 * θ))) + c * exp (-((x - c) ^ 2 / (2 * θ))) := by
    funext x; ring
  rw [e, integral_add (W3a_BoltzmannBGK_intPow c θ hθ 1)
    ((W3a_BoltzmannBGK_intExp c θ hθ).const_mul c), integral_const_mul,
    W3a_BoltzmannBGK_Iodd c θ 1 odd_one, W3a_BoltzmannBGK_I0 c θ hθ]
  ring

theorem W3a_BoltzmannBGK_sqrt_pow (θ : ℝ) (hθ : 0 < θ) :
    (2 * π * θ) ^ (3 / 2 : ℝ) = sqrt (2 * π * θ) ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-! ## One-dimensional Maxwellian (slab) -/

theorem W3a_BoltzmannBGK_m1 (ρ u θ : ℝ) (g : ℝ → ℝ) :
    ∫ w, g w * maxwellian1d ρ u θ w
      = ρ / sqrt (2 * π * θ) * ∫ w, g w * exp (-((w - u) ^ 2 / (2 * θ))) := by
  rw [← integral_const_mul]
  congr 1; funext w
  simp only [maxwellian1d, ← Real.sqrt_eq_rpow]
  ring

theorem W3a_BoltzmannBGK_m1int (ρ u θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    Integrable (fun w => (w - u) ^ n * maxwellian1d ρ u θ w) := by
  refine ((W3a_BoltzmannBGK_intPow u θ hθ n).const_mul
    (ρ / (2 * π * θ) ^ (1 / 2 : ℝ))).congr (ae_of_all _ fun w => ?_)
  simp only [maxwellian1d]
  ring

theorem W3a_BoltzmannBGK_facts1d (ρ u θ : ℝ) (hρ : 0 < ρ) (hθ : 0 < θ) :
    density1d (maxwellian1d ρ u θ) = ρ ∧ bulkVelocity1d (maxwellian1d ρ u θ) = u ∧
      (∫ w, (w - u) ^ 2 * maxwellian1d ρ u θ w) = ρ * θ ∧
      (∫ w, (w - u) ^ 3 * maxwellian1d ρ u θ w) = 0 ∧
      (∫ w, (w - u) ^ 1 * maxwellian1d ρ u θ w) = 0 ∧
      (∫ w, 2 * θ * maxwellian1d ρ u θ w) = 2 * θ * ρ := by
  have hs : 0 < sqrt (2 * π * θ) := by positivity
  have hMint : Integrable (maxwellian1d ρ u θ) := by
    simpa using W3a_BoltzmannBGK_m1int ρ u θ hθ 0
  have hd : ∫ w, maxwellian1d ρ u θ w = ρ := by
    have h := W3a_BoltzmannBGK_m1 ρ u θ (fun _ => 1)
    simp only [one_mul] at h
    rw [h, W3a_BoltzmannBGK_I0 u θ hθ]
    field_simp
  have hpow : ∀ n : ℕ, ∫ w, (w - u) ^ n * maxwellian1d ρ u θ w
      = ρ / sqrt (2 * π * θ) * ∫ w, (w - u) ^ n * exp (-((w - u) ^ 2 / (2 * θ))) :=
    fun n => W3a_BoltzmannBGK_m1 ρ u θ (fun w => (w - u) ^ n)
  have h1 : ∫ w, (w - u) ^ 1 * maxwellian1d ρ u θ w = 0 := by
    rw [hpow, W3a_BoltzmannBGK_Iodd u θ 1 odd_one, mul_zero]
  have h3 : ∫ w, (w - u) ^ 3 * maxwellian1d ρ u θ w = 0 := by
    rw [hpow, W3a_BoltzmannBGK_Iodd u θ 3 (by decide), mul_zero]
  have h2 : ∫ w, (w - u) ^ 2 * maxwellian1d ρ u θ w = ρ * θ := by
    rw [hpow, W3a_BoltzmannBGK_I2 u θ hθ]
    field_simp
  have hb : bulkVelocity1d (maxwellian1d ρ u θ) = u := by
    unfold bulkVelocity1d density1d
    have e : (fun w => w * maxwellian1d ρ u θ w) =
        fun w => (w - u) ^ 1 * maxwellian1d ρ u θ w + u * maxwellian1d ρ u θ w := by
      funext w; ring
    rw [e, integral_add (W3a_BoltzmannBGK_m1int ρ u θ hθ 1) (hMint.const_mul u),
      integral_const_mul, h1, hd, zero_add]
    field_simp
  refine ⟨hd, hb, h2, h3, h1, ?_⟩
  rw [integral_const_mul, hd]

/-! ## Products on Euclidean space -/

theorem W3a_BoltzmannBGK_prodInt {n : ℕ} (f : Fin n → ℝ → ℝ) :
    ∫ v : EuclideanSpace ℝ (Fin n), ∏ i, f i (v i) = ∏ i, ∫ x, f i x := by
  have h := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  exact (h.integral_comp' (fun y : Fin n → ℝ => ∏ i, f i (y i))).trans
    (integral_fintype_prod_volume_eq_prod (E := fun _ => ℝ) f)

theorem W3a_BoltzmannBGK_prodIntegrable {n : ℕ} (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Integrable (f i)) :
    Integrable (fun v : EuclideanSpace ℝ (Fin n) => ∏ i, f i (v i)) := by
  have h := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  have hi : Integrable (fun y : Fin n → ℝ => ∏ i, f i (y i)) :=
    Integrable.fintype_prod (μ := fun _ => volume) hf
  exact (h.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hi

theorem W3a_BoltzmannBGK_int2 (f0 f1 : ℝ → ℝ) :
    ∫ p : Perp, f0 (p 0) * f1 (p 1) = (∫ x, f0 x) * ∫ x, f1 x := by
  have := W3a_BoltzmannBGK_prodInt ![f0, f1]
  simpa [Fin.prod_univ_two] using this

theorem W3a_BoltzmannBGK_int2i (f0 f1 : ℝ → ℝ) (h0 : Integrable f0) (h1 : Integrable f1) :
    Integrable (fun p : Perp => f0 (p 0) * f1 (p 1)) := by
  have := W3a_BoltzmannBGK_prodIntegrable ![f0, f1] (by intro i; fin_cases i <;> simp [h0, h1])
  simpa [Fin.prod_univ_two] using this

/-! ## Three-dimensional Maxwellian -/

theorem W3a_BoltzmannBGK_expProd (θ : ℝ) (u v : Vel) :
    exp (-(‖v - u‖ ^ 2 / (2 * θ))) = ∏ i, exp (-((v i - u i) ^ 2 / (2 * θ))) := by
  rw [← Real.exp_sum, EuclideanSpace.real_norm_sq_eq, Finset.sum_div, ← Finset.sum_neg_distrib]
  simp only [PiLp.sub_apply]

theorem W3a_BoltzmannBGK_coordFun (ρ θ : ℝ) (u : Vel) (g : ℝ → ℝ) (j : Fin 3) (v : Vel) :
    g (v j) * maxwellian ρ u θ v = ρ / (2 * π * θ) ^ (3 / 2 : ℝ) *
      ∏ i, ((if i = j then g (v i) else 1) * exp (-((v i - u i) ^ 2 / (2 * θ)))) := by
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp only [Finset.mem_univ, if_true, maxwellian, W3a_BoltzmannBGK_expProd]
  ring

theorem W3a_BoltzmannBGK_coord (ρ θ : ℝ) (u : Vel) (hθ : 0 < θ) (g : ℝ → ℝ) (j : Fin 3) :
    ∫ v : Vel, g (v j) * maxwellian ρ u θ v =
      ρ / sqrt (2 * π * θ) * ∫ t, g t * exp (-((t - u j) ^ 2 / (2 * θ))) := by
  have hs : 0 < sqrt (2 * π * θ) := by positivity
  have e : (fun v : Vel => g (v j) * maxwellian ρ u θ v) = fun v => ρ / (2 * π * θ) ^ (3 / 2 : ℝ) *
      ∏ i, ((if i = j then g (v i) else 1) * exp (-((v i - u i) ^ 2 / (2 * θ)))) :=
    funext fun v => W3a_BoltzmannBGK_coordFun ρ θ u g j v
  have hP : (∫ v : Vel, ∏ i, ((if i = j then g (v i) else 1) * exp (-((v i - u i) ^ 2 / (2 * θ)))))
      = ∏ i, ∫ t, (if i = j then g t else 1) * exp (-((t - u i) ^ 2 / (2 * θ))) :=
    W3a_BoltzmannBGK_prodInt
      (fun i t => (if i = j then g t else 1) * exp (-((t - u i) ^ 2 / (2 * θ))))
  have hF : ∀ i, ∫ t, (if i = j then g t else 1) * exp (-((t - u i) ^ 2 / (2 * θ))) =
      (if i = j then (∫ t, g t * exp (-((t - u i) ^ 2 / (2 * θ)))) / sqrt (2 * π * θ) else 1) *
        sqrt (2 * π * θ) := by
    intro i
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, div_mul_cancel₀ _ hs.ne']
      simp
    · simp only [if_neg h, one_mul]
      exact W3a_BoltzmannBGK_I0 (u i) θ hθ
  rw [e, integral_const_mul, hP, Finset.prod_congr rfl (fun i _ => hF i),
    Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ _), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, W3a_BoltzmannBGK_sqrt_pow θ hθ]
  field_simp

theorem W3a_BoltzmannBGK_coordInt (ρ θ : ℝ) (u : Vel) (hθ : 0 < θ) (g : ℝ → ℝ) (j : Fin 3)
    (hg : Integrable (fun t => g t * exp (-((t - u j) ^ 2 / (2 * θ))))) :
    Integrable (fun v : Vel => g (v j) * maxwellian ρ u θ v) := by
  have h := W3a_BoltzmannBGK_prodIntegrable
    (fun i t => (if i = j then g t else 1) * exp (-((t - u i) ^ 2 / (2 * θ)))) (by
      intro i
      by_cases h : i = j
      · subst h; simpa using hg
      · simpa [h] using W3a_BoltzmannBGK_intExp (u i) θ hθ)
  refine (h.const_mul (ρ / (2 * π * θ) ^ (3 / 2 : ℝ))).congr (ae_of_all _ fun v => ?_)
  simp only [W3a_BoltzmannBGK_coordFun ρ θ u g j v]

theorem W3a_BoltzmannBGK_maxw_int (ρ θ : ℝ) (u : Vel) (hθ : 0 < θ) :
    Integrable (maxwellian ρ u θ) := by
  have := W3a_BoltzmannBGK_coordInt ρ θ u hθ (fun _ => 1) 0
    (by simpa using W3a_BoltzmannBGK_intExp (u 0) θ hθ)
  simpa using this

theorem W3a_BoltzmannBGK_maxw_int2 (ρ θ : ℝ) (u : Vel) (hθ : 0 < θ) :
    Integrable (fun v => ‖v‖ ^ 2 * maxwellian ρ u θ v) := by
  refine (integrable_finset_sum Finset.univ (fun j _ =>
    W3a_BoltzmannBGK_coordInt ρ θ u hθ (fun t => t ^ 2) j
      (W3a_BoltzmannBGK_intSq (u j) θ hθ))).congr (ae_of_all _ fun v => ?_)
  simp only [EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]

theorem solution (ρ θ : ℝ) (u : Vel) (hθ : 0 < θ) :
    ∫ v, maxwellian ρ u θ v = ρ := by
  have hs : 0 < sqrt (2 * π * θ) := by positivity
  have h := W3a_BoltzmannBGK_coord ρ θ u hθ (fun _ => 1) 0
  simp only [one_mul] at h
  rw [h, W3a_BoltzmannBGK_I0 (u 0) θ hθ]
  field_simp

theorem W3a_BoltzmannBGK_maxwellian_energy (ρ θ : ℝ) (u : Vel) (hθ : 0 < θ) :
    ∫ v, ‖v - u‖ ^ 2 * maxwellian ρ u θ v = 3 * ρ * θ := by
  have hs : 0 < sqrt (2 * π * θ) := by positivity
  have e : (fun v : Vel => ‖v - u‖ ^ 2 * maxwellian ρ u θ v) =
      fun v => ∑ j, (v j - u j) ^ 2 * maxwellian ρ u θ v := by
    funext v; simp only [EuclideanSpace.real_norm_sq_eq, Finset.sum_mul, PiLp.sub_apply]
  have hj : ∀ j : Fin 3, ∫ v : Vel, (v j - u j) ^ 2 * maxwellian ρ u θ v = ρ * θ := by
    intro j
    rw [W3a_BoltzmannBGK_coord ρ θ u hθ (fun t => (t - u j) ^ 2) j]
    rw [W3a_BoltzmannBGK_I2 (u j) θ hθ]
    field_simp
  rw [e, integral_finset_sum _ (fun j _ => W3a_BoltzmannBGK_coordInt ρ θ u hθ
    (fun t => (t - u j) ^ 2) j (W3a_BoltzmannBGK_intPow (u j) θ hθ 2))]
  simp only [hj, Fin.sum_univ_three]
  ring

theorem W3a_BoltzmannBGK_maxwellian_momentum (ρ θ : ℝ) (u : Vel) (hθ : 0 < θ) :
    ∫ v, maxwellian ρ u θ v • v = ρ • u := by
  have hs : 0 < sqrt (2 * π * θ) := by positivity
  have hi : Integrable fun v : Vel => maxwellian ρ u θ v • v := by
    refine Integrable.mono' ((W3a_BoltzmannBGK_maxw_int ρ θ u hθ).norm.add
      (W3a_BoltzmannBGK_maxw_int2 ρ θ u hθ).norm)
      ((W3a_BoltzmannBGK_maxw_int ρ θ u hθ).aestronglyMeasurable.smul
        continuous_id.aestronglyMeasurable) (ae_of_all _ fun v => ?_)
    simp only [norm_smul, Pi.add_apply, norm_mul, norm_pow, norm_norm]
    have h1 := norm_nonneg (maxwellian ρ u θ v)
    have h2 : ‖v‖ ≤ 1 + ‖v‖ ^ 2 := by nlinarith [sq_nonneg (‖v‖ - 1)]
    nlinarith [mul_le_mul_of_nonneg_left h2 h1]
  ext j
  have h1 := (EuclideanSpace.proj j : Vel →L[ℝ] ℝ).integral_comp_comm hi
  have h2 : ∫ v : Vel, (fun t => t) (v j) * maxwellian ρ u θ v = ρ * u j := by
    rw [W3a_BoltzmannBGK_coord ρ θ u hθ (fun t => t) j, W3a_BoltzmannBGK_I1lin (u j) θ hθ]
    field_simp
  have h3 : (∫ v, maxwellian ρ u θ v • v) j = ∫ v : Vel, (fun t => t) (v j) * maxwellian ρ u θ v := by
    change (EuclideanSpace.proj j) (∫ v, maxwellian ρ u θ v • v) = _
    rw [← h1]
    congr 1; funext v
    show (maxwellian ρ u θ v • v) j = v j * maxwellian ρ u θ v
    rw [PiLp.smul_apply, smul_eq_mul, mul_comm]
  rw [h3, h2, PiLp.smul_apply, smul_eq_mul]

theorem W3a_BoltzmannBGK_localMaxwellian_maxwellian (ρ θ : ℝ) (u : Vel) (hρ : 0 < ρ)
    (hθ : 0 < θ) :
    localMaxwellian (maxwellian ρ u θ) = maxwellian ρ u θ := by
  have hd : density (maxwellian ρ u θ) = ρ := solution ρ θ u hθ
  have hb : bulkVelocity (maxwellian ρ u θ) = u := by
    unfold bulkVelocity
    rw [hd, W3a_BoltzmannBGK_maxwellian_momentum ρ θ u hθ, inv_smul_smul₀ hρ.ne']
  have ht : temperature (maxwellian ρ u θ) = θ := by
    unfold temperature
    rw [hb, hd, W3a_BoltzmannBGK_maxwellian_energy ρ θ u hθ]
    field_simp
  unfold localMaxwellian
  rw [hd, hb, ht]

theorem W3a_BoltzmannBGK_maxwellian_isBGKSolution (τ ρ θ : ℝ) (u : Vel) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hθ : 0 < θ) :
    IsBGKSolution τ fun _ _ v => maxwellian ρ u θ v := by
  refine ⟨fun _ _ => differentiable_const _, fun _ _ => differentiable_const _, fun t x v => ?_⟩
  simp [collision, W3a_BoltzmannBGK_localMaxwellian_maxwellian ρ θ u hρ hθ]

/-! ## General kinetic states -/

theorem W3a_BoltzmannBGK_normsq_int (f : Vel → ℝ) (hf : Integrable f)
    (hf2 : Integrable fun v => ‖v‖ ^ 2 * f v) (c : Vel) :
    Integrable fun v => ‖v - c‖ ^ 2 * f v := by
  refine Integrable.mono' ((hf2.norm.const_mul 2).add (hf.norm.const_mul (2 * ‖c‖ ^ 2)))
    ((by fun_prop : Continuous fun v : Vel => ‖v - c‖ ^ 2).aestronglyMeasurable.mul
      hf.aestronglyMeasurable) (ae_of_all _ fun v => ?_)
  simp only [norm_mul, norm_pow, norm_norm, Pi.add_apply]
  have h1 := norm_sub_le v c
  have h2 : ‖v - c‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 + 2 * ‖c‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖v‖ - ‖c‖)]
  have h3 := norm_nonneg (f v)
  nlinarith [mul_le_mul_of_nonneg_right h2 h3]

theorem W3a_BoltzmannBGK_smul_int (f : Vel → ℝ) (hf : Integrable f)
    (hf2 : Integrable fun v => ‖v‖ ^ 2 * f v) : Integrable fun v => f v • v := by
  refine Integrable.mono' (hf.norm.add hf2.norm)
    (hf.aestronglyMeasurable.smul continuous_id.aestronglyMeasurable) (ae_of_all _ fun v => ?_)
  simp only [norm_smul, Pi.add_apply, norm_mul, norm_pow, norm_norm]
  have h1 := norm_nonneg (f v)
  have h2 : ‖v‖ ≤ 1 + ‖v‖ ^ 2 := by nlinarith [sq_nonneg (‖v‖ - 1)]
  nlinarith [mul_le_mul_of_nonneg_left h2 h1]

theorem W3a_BoltzmannBGK_dens_pos (f : Vel → ℝ) (hf : IsKineticState f) : 0 < density f := by
  unfold density
  rw [integral_pos_iff_support_of_nonneg (fun v => (hf.pos v).le) hf.integrable]
  have : Function.support f = Set.univ := Set.eq_univ_of_forall fun v => (hf.pos v).ne'
  rw [this]
  exact IsOpen.measure_pos volume isOpen_univ Set.univ_nonempty

theorem W3a_BoltzmannBGK_temp_pos (f : Vel → ℝ) (hf : IsKineticState f) :
    0 < temperature f := by
  have hρ := W3a_BoltzmannBGK_dens_pos f hf
  unfold temperature
  refine div_pos ?_ (by linarith)
  have hi := W3a_BoltzmannBGK_normsq_int f hf.integrable hf.integrable_sq (bulkVelocity f)
  rw [integral_pos_iff_support_of_nonneg
    (fun v => mul_nonneg (sq_nonneg _) (hf.pos v).le) hi]
  have hsub : ({bulkVelocity f}ᶜ : Set Vel) ⊆
      Function.support (fun v => ‖v - bulkVelocity f‖ ^ 2 * f v) := by
    intro v hv
    have h1 : v - bulkVelocity f ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hv)
    exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr h1)) (hf.pos v).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  obtain ⟨w, hw⟩ := exists_ne (bulkVelocity f)
  exact IsOpen.measure_pos volume isOpen_compl_singleton ⟨w, Set.mem_compl_singleton_iff.mpr hw⟩

theorem W3a_BoltzmannBGK_fv (f : Vel → ℝ) (hf : IsKineticState f) :
    ∫ v, f v • v = density f • bulkVelocity f := by
  have hρ := W3a_BoltzmannBGK_dens_pos f hf
  unfold bulkVelocity
  rw [smul_inv_smul₀ hρ.ne']

theorem W3a_BoltzmannBGK_ftemp (f : Vel → ℝ) (hf : IsKineticState f) :
    ∫ v, ‖v - bulkVelocity f‖ ^ 2 * f v = 3 * density f * temperature f := by
  have hρ := W3a_BoltzmannBGK_dens_pos f hf
  have hρ' := hρ.ne'
  unfold temperature
  field_simp

theorem W3a_BoltzmannBGK_LM (f : Vel → ℝ) (hf : IsKineticState f) :
    Integrable (localMaxwellian f) ∧ Integrable (fun v => ‖v‖ ^ 2 * localMaxwellian f v) ∧
    ∫ v, localMaxwellian f v = density f ∧
    ∫ v, localMaxwellian f v • v = density f • bulkVelocity f ∧
    ∫ v, ‖v - bulkVelocity f‖ ^ 2 * localMaxwellian f v = 3 * density f * temperature f ∧
    (∀ v, 0 < localMaxwellian f v) := by
  have hρ := W3a_BoltzmannBGK_dens_pos f hf
  have hθ := W3a_BoltzmannBGK_temp_pos f hf
  refine ⟨W3a_BoltzmannBGK_maxw_int (density f) (temperature f) (bulkVelocity f) hθ,
    W3a_BoltzmannBGK_maxw_int2 (density f) (temperature f) (bulkVelocity f) hθ,
    solution (density f) (temperature f) (bulkVelocity f) hθ,
    W3a_BoltzmannBGK_maxwellian_momentum (density f) (temperature f) (bulkVelocity f) hθ,
    W3a_BoltzmannBGK_maxwellian_energy (density f) (temperature f) (bulkVelocity f) hθ,
    fun v => ?_⟩
  unfold localMaxwellian maxwellian
  positivity

theorem W3a_BoltzmannBGK_collision_conserves_mass (τ : ℝ) (f : Vel → ℝ) (hτ : 0 < τ)
    (hf : IsKineticState f) :
    ∫ v, collision τ f v = 0 := by
  obtain ⟨hMi, -, hMint, -, -, -⟩ := W3a_BoltzmannBGK_LM f hf
  unfold collision
  rw [integral_const_mul, integral_sub hf.integrable hMi, hMint]
  unfold density
  ring

theorem W3a_BoltzmannBGK_collision_conserves_momentum (τ : ℝ) (f : Vel → ℝ) (hτ : 0 < τ)
    (hf : IsKineticState f) :
    ∫ v, collision τ f v • v = 0 := by
  obtain ⟨hMi, hMi2, -, hMmom, -, -⟩ := W3a_BoltzmannBGK_LM f hf
  have hfv := W3a_BoltzmannBGK_fv f hf
  have e : (fun v => collision τ f v • v) =
      fun v => (-(1 / τ)) • (f v • v - localMaxwellian f v • v) := by
    funext v; simp only [collision, mul_smul, sub_smul]
  rw [e, integral_smul, integral_sub (W3a_BoltzmannBGK_smul_int f hf.integrable hf.integrable_sq)
    (W3a_BoltzmannBGK_smul_int _ hMi hMi2), hfv, hMmom, sub_self, smul_zero]

theorem W3a_BoltzmannBGK_Q (g : Vel → ℝ) (hg : Integrable g)
    (hg2 : Integrable fun v => ‖v‖ ^ 2 * g v) (u : Vel) :
    ∫ v, ‖v‖ ^ 2 * g v = (∫ v, ‖v - u‖ ^ 2 * g v) + 2 * inner ℝ u (∫ v, g v • v)
      - ‖u‖ ^ 2 * ∫ v, g v := by
  have h1 := W3a_BoltzmannBGK_normsq_int g hg hg2 u
  have h2 := W3a_BoltzmannBGK_smul_int g hg hg2
  have h3 : Integrable fun v => inner ℝ u (g v • v) := h2.const_inner u
  have e : (fun v => ‖v‖ ^ 2 * g v) = fun v =>
      (‖v - u‖ ^ 2 * g v + 2 * inner ℝ u (g v • v)) - ‖u‖ ^ 2 * g v := by
    funext v
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm u v]
    ring
  have i4 : Integrable (fun v => ‖v - u‖ ^ 2 * g v + 2 * inner ℝ u (g v • v)) :=
    h1.add (h3.const_mul 2)
  have i5 : Integrable (fun v => 2 * inner ℝ u (g v • v)) := h3.const_mul 2
  have i6 : Integrable (fun v => ‖u‖ ^ 2 * g v) := hg.const_mul _
  rw [e, integral_sub i4 i6, integral_add h1 i5,
    integral_const_mul, integral_const_mul, integral_inner h2 u]

theorem W3a_BoltzmannBGK_collision_conserves_energy (τ : ℝ) (f : Vel → ℝ) (hτ : 0 < τ)
    (hf : IsKineticState f) :
    ∫ v, ‖v‖ ^ 2 * collision τ f v = 0 := by
  obtain ⟨hMi, hMi2, hMint, hMmom, hMen, -⟩ := W3a_BoltzmannBGK_LM f hf
  have hfv := W3a_BoltzmannBGK_fv f hf
  have hft := W3a_BoltzmannBGK_ftemp f hf
  have e : (fun v => ‖v‖ ^ 2 * collision τ f v) =
      fun v => -(1 / τ) * (‖v‖ ^ 2 * f v - ‖v‖ ^ 2 * localMaxwellian f v) := by
    funext v; simp only [collision]; ring
  rw [e, integral_const_mul, integral_sub hf.integrable_sq hMi2,
    W3a_BoltzmannBGK_Q f hf.integrable hf.integrable_sq (bulkVelocity f),
    W3a_BoltzmannBGK_Q _ hMi hMi2 (bulkVelocity f), hMint, hMmom, hMen, hfv, hft]
  have hd : ∫ v, f v = density f := rfl
  rw [hd]
  ring

/-! ## H-theorem -/

theorem W3a_BoltzmannBGK_logpair (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (log a - log b) * (a - b) ∧ ((log a - log b) * (a - b) = 0 ↔ a = b) := by
  rcases lt_trichotomy a b with h | h | h
  · have hl := Real.log_lt_log ha h
    have hp : 0 < (log a - log b) * (a - b) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
    exact ⟨hp.le, ⟨fun h' => absurd h' hp.ne', fun h' => absurd h' h.ne⟩⟩
  · subst h; simp
  · have hl := Real.log_lt_log hb h
    have hp : 0 < (log a - log b) * (a - b) := mul_pos (by linarith) (by linarith)
    exact ⟨hp.le, ⟨fun h' => absurd h' hp.ne', fun h' => absurd h' h.ne'⟩⟩

theorem W3a_BoltzmannBGK_Hcore (τ : ℝ) (f : Vel → ℝ) (hτ : 0 < τ) (hf : IsKineticState f)
    (hint : Integrable fun v => Real.log (f v) * collision τ f v) :
    ∃ D : Vel → ℝ, Integrable D ∧ (∀ v, 0 ≤ D v) ∧
      (∀ v, D v = 0 ↔ f v = localMaxwellian f v) ∧
      ∫ v, Real.log (f v) * collision τ f v = -(1 / τ) * ∫ v, D v := by
  obtain ⟨hMi, hMi2, hMint, -, hMen, hMpos⟩ := W3a_BoltzmannBGK_LM f hf
  have hρ := W3a_BoltzmannBGK_dens_pos f hf
  have hθ := W3a_BoltzmannBGK_temp_pos f hf
  have hft := W3a_BoltzmannBGK_ftemp f hf
  have hfi := hf.integrable
  have h1f := W3a_BoltzmannBGK_normsq_int f hfi hf.integrable_sq (bulkVelocity f)
  have h1M := W3a_BoltzmannBGK_normsq_int _ hMi hMi2 (bulkVelocity f)
  set K := density f / (2 * π * temperature f) ^ (3 / 2 : ℝ) with hKdef
  have hK : 0 < K := by rw [hKdef]; positivity
  have hlogM : ∀ v, log (localMaxwellian f v) =
      log K - ‖v - bulkVelocity f‖ ^ 2 / (2 * temperature f) := by
    intro v
    simp only [localMaxwellian, maxwellian]
    rw [Real.log_mul hK.ne' (exp_pos _).ne', Real.log_exp]
    ring
  have hτ1 : τ * (1 / τ) = 1 := mul_one_div_cancel hτ.ne'
  have hA : Integrable fun v => log (f v) * (f v - localMaxwellian f v) := by
    refine (hint.const_mul (-τ)).congr (ae_of_all _ fun v => ?_)
    simp only [collision]
    linear_combination (log (f v) * (f v - localMaxwellian f v)) * hτ1
  have eB : (fun v => log (localMaxwellian f v) * (f v - localMaxwellian f v)) = fun v =>
      log K * (f v - localMaxwellian f v) - (1 / (2 * temperature f)) *
        (‖v - bulkVelocity f‖ ^ 2 * f v - ‖v - bulkVelocity f‖ ^ 2 * localMaxwellian f v) := by
    funext v; rw [hlogM v]; ring
  have hB : Integrable fun v => log (localMaxwellian f v) * (f v - localMaxwellian f v) := by
    rw [eB]
    exact ((hfi.sub hMi).const_mul _).sub ((h1f.sub h1M).const_mul _)
  have j1 : Integrable (fun v => log K * (f v - localMaxwellian f v)) := (hfi.sub hMi).const_mul _
  have j2 : Integrable (fun v => (1 / (2 * temperature f)) *
      (‖v - bulkVelocity f‖ ^ 2 * f v - ‖v - bulkVelocity f‖ ^ 2 * localMaxwellian f v)) :=
    (h1f.sub h1M).const_mul _
  have hB0 : ∫ v, log (localMaxwellian f v) * (f v - localMaxwellian f v) = 0 := by
    rw [eB, integral_sub j1 j2,
      integral_const_mul, integral_const_mul, integral_sub hfi hMi, integral_sub h1f h1M,
      hMint, hMen, hft]
    have hd : ∫ v, f v = density f := rfl
    rw [hd]
    ring
  refine ⟨fun v => (log (f v) - log (localMaxwellian f v)) * (f v - localMaxwellian f v),
    ?_, fun v => (W3a_BoltzmannBGK_logpair _ _ (hf.pos v) (hMpos v)).1,
    fun v => (W3a_BoltzmannBGK_logpair _ _ (hf.pos v) (hMpos v)).2, ?_⟩
  · exact (hA.sub hB).congr (ae_of_all _ fun v => by simp only [Pi.sub_apply]; ring)
  · have eD : (fun v => (log (f v) - log (localMaxwellian f v)) * (f v - localMaxwellian f v)) =
        fun v => log (f v) * (f v - localMaxwellian f v) -
          log (localMaxwellian f v) * (f v - localMaxwellian f v) := by
      funext v; ring
    have eC : (fun v => Real.log (f v) * collision τ f v) =
        fun v => -(1 / τ) * (log (f v) * (f v - localMaxwellian f v)) := by
      funext v; simp only [collision]; ring
    rw [eD, integral_sub hA hB, hB0, sub_zero, eC, integral_const_mul]

theorem W3a_BoltzmannBGK_entropy_production_nonpos (τ : ℝ) (f : Vel → ℝ) (hτ : 0 < τ)
    (hf : IsKineticState f)
    (hint : Integrable fun v => Real.log (f v) * collision τ f v) :
    ∫ v, Real.log (f v) * collision τ f v ≤ 0 := by
  obtain ⟨D, -, hD0, -, heq⟩ := W3a_BoltzmannBGK_Hcore τ f hτ hf hint
  rw [heq]
  have h1 : 0 ≤ ∫ v, D v := integral_nonneg hD0
  have h2 : 0 < 1 / τ := one_div_pos.mpr hτ
  nlinarith [mul_nonneg h2.le h1]

theorem W3a_BoltzmannBGK_bgk_H_theorem (τ : ℝ) (f : Vel → ℝ) (hτ : 0 < τ) (hf : IsKineticState f)
    (hint : Integrable fun v => Real.log (f v) * collision τ f v) :
    (∫ v, Real.log (f v) * collision τ f v ≤ 0) ∧
      ((∫ v, Real.log (f v) * collision τ f v = 0) ↔
        f =ᵐ[volume] localMaxwellian f) := by
  refine ⟨W3a_BoltzmannBGK_entropy_production_nonpos τ f hτ hf hint, ?_⟩
  obtain ⟨D, hDi, hD0, hDz, heq⟩ := W3a_BoltzmannBGK_Hcore τ f hτ hf hint
  have hτ' : -(1 / τ) ≠ 0 := by
    have : 0 < 1 / τ := one_div_pos.mpr hτ
    linarith
  rw [heq]
  constructor
  · intro h
    have h0 : ∫ v, D v = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hτ'
      · exact h'
    have hae := (integral_eq_zero_iff_of_nonneg (fun v => hD0 v) hDi).mp h0
    filter_upwards [hae] with v hv
    exact (hDz v).mp hv
  · intro h
    have hae : D =ᵐ[volume] 0 := by
      filter_upwards [h] with v hv
      exact (hDz v).mpr hv
    rw [integral_eq_zero_of_ae hae, mul_zero]

/-! ## Slab reductions -/

theorem W3a_BoltzmannBGK_I0z (θ : ℝ) (hθ : 0 < θ) :
    ∫ x : ℝ, exp (-(x ^ 2 / (2 * θ))) = sqrt (2 * π * θ) := by
  simpa using W3a_BoltzmannBGK_I0 0 θ hθ

theorem W3a_BoltzmannBGK_I2z (θ : ℝ) (hθ : 0 < θ) :
    ∫ x : ℝ, x ^ 2 * exp (-(x ^ 2 / (2 * θ))) = θ * sqrt (2 * π * θ) := by
  simpa using W3a_BoltzmannBGK_I2 0 θ hθ

theorem W3a_BoltzmannBGK_slabSplit (ρ u θ w : ℝ) (p : Perp) :
    maxwellianSlab ρ u θ w p = (ρ / (2 * π * θ) ^ (3 / 2 : ℝ) * exp (-((w - u) ^ 2 / (2 * θ)))) *
      (exp (-(p 0 ^ 2 / (2 * θ))) * exp (-(p 1 ^ 2 / (2 * θ)))) := by
  simp only [maxwellianSlab]
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hx : exp (-(((w - u) ^ 2 + (p 0 ^ 2 + p 1 ^ 2)) / (2 * θ))) = exp (-((w - u) ^ 2 / (2 * θ))) *
      (exp (-(p 0 ^ 2 / (2 * θ))) * exp (-(p 1 ^ 2 / (2 * θ)))) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hx]; ring

theorem W3a_BoltzmannBGK_reduceG_maxwellianSlab (ρ u θ : ℝ) (hθ : 0 < θ) :
    reduceG (maxwellianSlab ρ u θ) = maxwellian1d ρ u θ := by
  have hs : 0 < sqrt (2 * π * θ) := by positivity
  funext w
  have h2 : ∫ p : Perp, exp (-(p 0 ^ 2 / (2 * θ))) * exp (-(p 1 ^ 2 / (2 * θ)))
      = sqrt (2 * π * θ) * sqrt (2 * π * θ) := by
    rw [W3a_BoltzmannBGK_int2 (fun x => exp (-(x ^ 2 / (2 * θ))))
      (fun x => exp (-(x ^ 2 / (2 * θ)))), W3a_BoltzmannBGK_I0z θ hθ]
  simp only [reduceG]
  rw [integral_congr_ae (ae_of_all _ (W3a_BoltzmannBGK_slabSplit ρ u θ w)), integral_const_mul, h2]
  simp only [maxwellian1d]
  rw [W3a_BoltzmannBGK_sqrt_pow θ hθ, ← Real.sqrt_eq_rpow]
  field_simp

theorem W3a_BoltzmannBGK_reduceH_maxwellianSlab (ρ u θ : ℝ) (hθ : 0 < θ) :
    reduceH (maxwellianSlab ρ u θ) = fun w => 2 * θ * maxwellian1d ρ u θ w := by
  have hs : 0 < sqrt (2 * π * θ) := by positivity
  have hss : sqrt (2 * π * θ) * sqrt (2 * π * θ) = 2 * π * θ := Real.mul_self_sqrt (by positivity)
  funext w
  have hA : ∫ p : Perp, p 0 ^ 2 * exp (-(p 0 ^ 2 / (2 * θ))) * exp (-(p 1 ^ 2 / (2 * θ)))
      = θ * sqrt (2 * π * θ) * sqrt (2 * π * θ) := by
    rw [W3a_BoltzmannBGK_int2 (fun x => x ^ 2 * exp (-(x ^ 2 / (2 * θ))))
      (fun x => exp (-(x ^ 2 / (2 * θ)))), W3a_BoltzmannBGK_I0z θ hθ, W3a_BoltzmannBGK_I2z θ hθ]
  have hB : ∫ p : Perp, exp (-(p 0 ^ 2 / (2 * θ))) * (p 1 ^ 2 * exp (-(p 1 ^ 2 / (2 * θ))))
      = sqrt (2 * π * θ) * (θ * sqrt (2 * π * θ)) := by
    rw [W3a_BoltzmannBGK_int2 (fun x => exp (-(x ^ 2 / (2 * θ))))
      (fun x => x ^ 2 * exp (-(x ^ 2 / (2 * θ)))), W3a_BoltzmannBGK_I0z θ hθ,
      W3a_BoltzmannBGK_I2z θ hθ]
  have iE : Integrable (fun x : ℝ => exp (-(x ^ 2 / (2 * θ)))) := by
    simpa using W3a_BoltzmannBGK_intExp 0 θ hθ
  have iS : Integrable (fun x : ℝ => x ^ 2 * exp (-(x ^ 2 / (2 * θ)))) := by
    simpa using W3a_BoltzmannBGK_intPow 0 θ hθ 2
  have iA : Integrable (fun p : Perp =>
      p 0 ^ 2 * exp (-(p 0 ^ 2 / (2 * θ))) * exp (-(p 1 ^ 2 / (2 * θ)))) :=
    W3a_BoltzmannBGK_int2i (fun x => x ^ 2 * exp (-(x ^ 2 / (2 * θ))))
      (fun x => exp (-(x ^ 2 / (2 * θ)))) iS iE
  have iB : Integrable (fun p : Perp =>
      exp (-(p 0 ^ 2 / (2 * θ))) * (p 1 ^ 2 * exp (-(p 1 ^ 2 / (2 * θ))))) :=
    W3a_BoltzmannBGK_int2i (fun x => exp (-(x ^ 2 / (2 * θ))))
      (fun x => x ^ 2 * exp (-(x ^ 2 / (2 * θ)))) iE iS
  have hpt : ∀ p : Perp, ‖p‖ ^ 2 * maxwellianSlab ρ u θ w p =
      (ρ / (2 * π * θ) ^ (3 / 2 : ℝ) * exp (-((w - u) ^ 2 / (2 * θ)))) *
        (p 0 ^ 2 * exp (-(p 0 ^ 2 / (2 * θ))) * exp (-(p 1 ^ 2 / (2 * θ))) +
          exp (-(p 0 ^ 2 / (2 * θ))) * (p 1 ^ 2 * exp (-(p 1 ^ 2 / (2 * θ))))) := by
    intro p
    rw [W3a_BoltzmannBGK_slabSplit, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    ring
  simp only [reduceH]
  rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul, integral_add iA iB, hA, hB]
  simp only [maxwellian1d]
  rw [W3a_BoltzmannBGK_sqrt_pow θ hθ, ← Real.sqrt_eq_rpow]
  field_simp
  ring

theorem W3a_BoltzmannBGK_maxwellian1d_moments (ρ u θ : ℝ) (hρ : 0 < ρ) (hθ : 0 < θ) :
    density1d (maxwellian1d ρ u θ) = ρ ∧
      bulkVelocity1d (maxwellian1d ρ u θ) = u ∧
      temperature1d (maxwellian1d ρ u θ) (fun w => 2 * θ * maxwellian1d ρ u θ w) = θ := by
  obtain ⟨hd, hb, h2, -, -, h2θ⟩ := W3a_BoltzmannBGK_facts1d ρ u θ hρ hθ
  refine ⟨hd, hb, ?_⟩
  simp only [temperature1d]
  rw [hb, hd, h2, h2θ]
  field_simp
  ring

theorem W3a_BoltzmannBGK_equilibrium_stressT_heatFlux (ρ u θ : ℝ) (hρ : 0 < ρ) (hθ : 0 < θ) :
    stressT (maxwellian1d ρ u θ) (fun w => 2 * θ * maxwellian1d ρ u θ w) = 0 ∧
      heatFlux (maxwellian1d ρ u θ) (fun w => 2 * θ * maxwellian1d ρ u θ w) = 0 := by
  obtain ⟨hd, hb, -, h3, h1, h2θ⟩ := W3a_BoltzmannBGK_facts1d ρ u θ hρ hθ
  obtain ⟨-, -, ht⟩ := W3a_BoltzmannBGK_maxwellian1d_moments ρ u θ hρ hθ
  refine ⟨?_, ?_⟩
  · simp only [stressT]
    rw [hd, ht, h2θ]
    ring
  · simp only [heatFlux]
    rw [hb, h3]
    have e : ∫ v, (v - u) * (2 * θ * maxwellian1d ρ u θ v)
        = 2 * θ * ∫ v, (v - u) ^ 1 * maxwellian1d ρ u θ v := by
      rw [← integral_const_mul]; congr 1; funext v; ring
    rw [e, h1]
    ring
