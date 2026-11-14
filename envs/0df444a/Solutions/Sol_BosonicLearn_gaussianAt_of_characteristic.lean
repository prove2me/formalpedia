-- Prove2me | solution 1 for BosonicLearn.gaussianAt_of_characteristic
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T20:38:06.7692+00:00
-- url     : https://prove2.me/submissions/b7f85d63-71b2-4fad-b9ba-7cad30dba9d0

import Mathlib
import Definitions.Def_BosonicLearn_husimiQ
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Theorems.Thm_BosonicLearn_husimi_fourier
import Theorems.Thm_BosonicLearn_photonEnergy_le_husimi

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

open BosonicLearn

/-!
# A state with a Gaussian characteristic function satisfies `GaussianAt`

* Symmetry of `γ` and the characteristic identity are hypotheses; convergence of the Weyl series is
  the first conjunct of `husimi_fourier`.
* The two derivative clauses are a direct computation with `t ↦ exp(-t² q/4 + i t m)`.
* Finite energy: by the argument of `eq_207`, the Husimi law is Mathlib's `multivariateGaussian`,
  which has a finite second moment (`IsGaussian.memLp_two_id`); `photonEnergy_le_husimi` bounds
  the photon number by that second moment.
-/

noncomputable section

/-- The bijection from grouped to interleaved quadrature labels. -/
private def grp {n : ℕ} : Fin n ⊕ Fin n → Fin n × Fin 2 :=
  Sum.elim (fun j => (j, 0)) (fun j => (j, 1))

private lemma meanForm_interleave {n : ℕ} (d : Fin n × Fin 2 → ℝ) (t : Fin n ⊕ Fin n → ℝ) :
    meanForm d (fun a : Fin n × Fin 2 => if a.2 = 0 then t (Sum.inl a.1) else t (Sum.inr a.1)) =
      ∑ a, t a * d (grp a) := by
  unfold meanForm
  rw [Fintype.sum_prod_type, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_two]
  simp [grp]

private lemma varianceForm_interleave {n : ℕ} (γ : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (t : Fin n ⊕ Fin n → ℝ) :
    varianceForm γ
      (fun a : Fin n × Fin 2 => if a.2 = 0 then t (Sum.inl a.1) else t (Sum.inr a.1)) =
      2 * ∑ a, ∑ b, t a * (γ (grp a) (grp b) / 2) * t b := by
  simp only [varianceForm, Fintype.sum_prod_type, Fintype.sum_sum_type, Fin.sum_univ_two]
  have h2 : ∀ a b c : ℝ, a * (b / 2) * c = (a * b * c) / 2 := fun a b c => by ring
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, Finset.sum_add_distrib, grp, Sum.elim_inl,
    Sum.elim_inr, h2, ← Finset.sum_div]
  ring

private lemma meanForm_smul {n : ℕ} (d ξ : Fin n × Fin 2 → ℝ) (t : ℝ) :
    meanForm d (t • ξ) = t * meanForm d ξ := by
  unfold meanForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma varianceForm_smul {n : ℕ} (γ : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (ξ : Fin n × Fin 2 → ℝ) (t : ℝ) :
    varianceForm γ (t • ξ) = t ^ 2 * varianceForm γ ξ := by
  unfold varianceForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma charFun_density {ι : Type*} [Fintype ι] (Q : (ι → ℝ) → ℝ) (hQ0 : ∀ β, 0 ≤ Q β)
    (hQm : Measurable Q) (x : EuclideanSpace ℝ ι) :
    charFun ((volume : Measure (EuclideanSpace ℝ ι)).withDensity
        (fun β => ENNReal.ofReal (Q (WithLp.ofLp β)))) x =
      ∫ β : ι → ℝ, Complex.exp (Complex.I * ((∑ a, x a * β a : ℝ) : ℂ)) * ((Q β : ℝ) : ℂ) := by
  rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  rw [← (PiLp.volume_preserving_ofLp ι).integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
  simp [ENNReal.toReal_ofReal (hQ0 _), PiLp.inner_apply, mul_comm]

private lemma integrable_density {ι : Type*} [Fintype ι] (Q : (ι → ℝ) → ℝ) (hQi : Integrable Q) :
    Integrable (fun β : EuclideanSpace ℝ ι => Q (WithLp.ofLp β)) :=
  ((PiLp.volume_preserving_ofLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurableEmbedding).2 hQi

/-- The first two derivatives at `0` of `t ↦ exp(-t² q/4 + i t m)`. -/
private lemma deriv_clauses (q m : ℝ) (χ : ℝ → ℂ)
    (hχ : ∀ t : ℝ, χ t =
      Complex.exp (((-(t ^ 2 * q) / 4 : ℝ) : ℂ) + Complex.I * ((t * m : ℝ) : ℂ))) :
    HasDerivAt χ (Complex.I * (m : ℂ)) 0 ∧
    HasDerivAt (deriv χ) (((-q / 2 - m ^ 2 : ℝ) : ℂ)) 0 := by
  have hfun : χ = fun t : ℝ =>
      Complex.exp (-(q : ℂ) / 4 * (t : ℂ) ^ 2 + Complex.I * (m : ℂ) * (t : ℂ)) := by
    funext t
    rw [hχ]
    congr 1
    push_cast
    ring
  have hid : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := fun t => by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hg : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => -(q : ℂ) / 4 * (t : ℂ) ^ 2 + Complex.I * (m : ℂ) * (t : ℂ))
      (-(q : ℂ) / 2 * (t : ℂ) + Complex.I * (m : ℂ)) t := by
    intro t
    have h1 : HasDerivAt
        (fun t : ℝ => -(q : ℂ) / 4 * (t : ℂ) ^ 2 + Complex.I * (m : ℂ) * (t : ℂ))
        (-(q : ℂ) / 4 * (((2 : ℕ) : ℂ) * (t : ℂ) ^ (2 - 1) * 1) + Complex.I * (m : ℂ) * 1) t :=
      (((hid t).pow 2).const_mul (-(q : ℂ) / 4)).add ((hid t).const_mul (Complex.I * (m : ℂ)))
    refine h1.congr_deriv ?_
    push_cast
    ring
  have hd : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => Complex.exp (-(q : ℂ) / 4 * (t : ℂ) ^ 2 + Complex.I * (m : ℂ) * (t : ℂ)))
      (Complex.exp (-(q : ℂ) / 4 * (t : ℂ) ^ 2 + Complex.I * (m : ℂ) * (t : ℂ)) *
        (-(q : ℂ) / 2 * (t : ℂ) + Complex.I * (m : ℂ))) t := fun t => (hg t).cexp
  have hderiv : deriv (fun t : ℝ =>
      Complex.exp (-(q : ℂ) / 4 * (t : ℂ) ^ 2 + Complex.I * (m : ℂ) * (t : ℂ))) =
      fun t : ℝ => Complex.exp (-(q : ℂ) / 4 * (t : ℂ) ^ 2 + Complex.I * (m : ℂ) * (t : ℂ)) *
        (-(q : ℂ) / 2 * (t : ℂ) + Complex.I * (m : ℂ)) := funext fun t => (hd t).deriv
  rw [hfun, hderiv]
  constructor
  · have h := hd 0
    refine h.congr_deriv ?_
    simp
  · have h3 : HasDerivAt (fun t : ℝ => -(q : ℂ) / 2 * (t : ℂ) + Complex.I * (m : ℂ))
        (-(q : ℂ) / 2) 0 := by
      have h4 := ((hid 0).const_mul (-(q : ℂ) / 2)).add_const (Complex.I * (m : ℂ))
      simpa using h4
    have h2 := (hd 0).mul h3
    refine h2.congr_deriv ?_
    simp only [Complex.ofReal_zero, mul_zero, zero_add, Complex.exp_zero, one_mul, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    push_cast
    linear_combination ((m : ℂ) ^ 2) * Complex.I_sq

/-- A state whose characteristic function is Gaussian in grouped coordinates has a Gaussian
Husimi law (the argument of `eq_207`). -/
private lemma husimi_law_gaussian {n : ℕ} (ρ : State (Occupation (Fin n)))
    (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hS : Sᵀ = S)
    (hchar : ∀ t : Fin n ⊕ Fin n → ℝ, oscillatorCharacteristic ρ.coefficients
        (fun a : Fin n × Fin 2 => if a.2 = 0 then t (Sum.inl a.1) else t (Sum.inr a.1)) =
      Complex.exp (((-(2 * ∑ a, ∑ b, t a * S a b * t b) / 4 : ℝ) : ℂ) +
        Complex.I * ((∑ a, t a * μ a : ℝ) : ℂ))) :
    (volume : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n))).withDensity
        (fun β => ENNReal.ofReal (husimiQ ρ.coefficients (WithLp.ofLp β))) =
      multivariateGaussian (WithLp.toLp 2 μ) (S + (1 / 2 : ℝ) • 1) := by
  obtain ⟨-, hQ0, hQm, hQi, hF⟩ := husimi_fourier ρ
  -- the characteristic function of the Husimi law
  have hcf : ∀ x : EuclideanSpace ℝ (Fin n ⊕ Fin n),
      charFun ((volume : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n))).withDensity
        (fun β => ENNReal.ofReal (husimiQ ρ.coefficients (WithLp.ofLp β)))) x =
      Complex.exp (((∑ a, x a * μ a : ℝ) : ℂ) * Complex.I -
        ((∑ a, ∑ b, x a * S a b * x b + (1 / 2) * ∑ a, x a ^ 2 : ℝ) : ℂ) / 2) := by
    intro x
    rw [charFun_density _ hQ0 hQm x, hF, hchar, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfin : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n))).withDensity
        (fun β => ENNReal.ofReal (husimiQ ρ.coefficients (WithLp.ofLp β)))) :=
    isFiniteMeasure_withDensity_ofReal (integrable_density _ hQi).2
  have hmass : ((volume : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n))).withDensity
        (fun β => ENNReal.ofReal (husimiQ ρ.coefficients (WithLp.ofLp β)))).real Set.univ = 1 := by
    have h0 := hcf 0
    rw [charFun_zero] at h0
    have : ((((volume : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n))).withDensity
        (fun β => ENNReal.ofReal (husimiQ ρ.coefficients (WithLp.ofLp β)))).real Set.univ : ℝ) : ℂ)
        = 1 := by
      rw [h0]; simp
    exact_mod_cast this
  have hquad : ∀ x : Fin n ⊕ Fin n → ℝ, x ⬝ᵥ (S + (1 / 2 : ℝ) • 1) *ᵥ x =
      ∑ a, ∑ b, x a * S a b * x b + (1 / 2) * ∑ a, x a ^ 2 := by
    intro x
    simp only [dotProduct, Matrix.mulVec, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    have hb : ∀ b, x a * ((S a b + 1 / 2 * (if a = b then 1 else 0)) * x b) =
        x a * S a b * x b + if a = b then 1 / 2 * x a ^ 2 else 0 := by
      intro b
      split_ifs with h
      · subst h; ring
      · ring
    simp only [hb, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hpsd : (S + (1 / 2 : ℝ) • 1).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · show (S + (1 / 2 : ℝ) • 1)ᴴ = _
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_add,
        Matrix.transpose_smul, Matrix.transpose_one, hS]
    · have h := norm_charFun_le (μ := (volume : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n))).withDensity
        (fun β => ENNReal.ofReal (husimiQ ρ.coefficients (WithLp.ofLp β)))) (WithLp.toLp 2 x)
      rw [hmass, hcf, Complex.norm_exp] at h
      rw [star_trivial, hquad]
      have h' := Real.exp_le_one_iff.mp h
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.div_ofNat_re, mul_zero, zero_mul, sub_zero,
        zero_sub] at h'
      linarith
  refine Measure.ext_of_charFun (funext fun x => ?_)
  rw [hcf, charFun_multivariateGaussian hpsd, hquad]
  congr 2
  simp [PiLp.inner_apply, mul_comm]

/-- Finite mean photon number: the Husimi law is a Gaussian measure, hence has a finite second
moment, which dominates the photon number. -/
private lemma energy_finite {n : ℕ} (ρ : State (Occupation (Fin n)))
    (d : Fin n × Fin 2 → ℝ) (γ : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (hγ : γ.transpose = γ)
    (h : ∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic ρ.coefficients ξ =
      Complex.exp (((-varianceForm γ ξ / 4 : ℝ) : ℂ) + Complex.I * (meanForm d ξ : ℂ))) :
    photonEnergy ρ.coefficients < ⊤ := by
  obtain ⟨-, hQ0, hQm, -, -⟩ := husimi_fourier ρ
  have hS : (Matrix.of fun a b : Fin n ⊕ Fin n => γ (grp a) (grp b) / 2)ᵀ =
      Matrix.of fun a b : Fin n ⊕ Fin n => γ (grp a) (grp b) / 2 := by
    ext i j
    have hij := congr_fun (congr_fun hγ (grp i)) (grp j)
    rw [Matrix.transpose_apply] at hij
    rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply, hij]
  have hνG := husimi_law_gaussian ρ (fun a => d (grp a))
    (Matrix.of fun a b : Fin n ⊕ Fin n => γ (grp a) (grp b) / 2) hS
    (fun t => by
      rw [h, meanForm_interleave, varianceForm_interleave]
      simp only [Matrix.of_apply])
  -- a Gaussian measure has a finite second moment
  have hmem : MemLp id 2 ((volume : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n))).withDensity
        (fun β => ENNReal.ofReal (husimiQ ρ.coefficients (WithLp.ofLp β)))) := by
    rw [hνG]
    exact IsGaussian.memLp_two_id
  have hint := (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).1 hmem
  have hlt := hint.lintegral_lt_top
  refine lt_of_le_of_lt (photonEnergy_le_husimi ρ) (lt_of_le_of_lt ?_ hlt)
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    ← (PiLp.volume_preserving_ofLp (Fin n ⊕ Fin n)).lintegral_comp_emb
      (MeasurableEquiv.toLp 2 (Fin n ⊕ Fin n → ℝ)).symm.measurableEmbedding]
  refine lintegral_mono fun β => ?_
  simp only [Pi.mul_apply, id_eq]
  rw [← ENNReal.ofReal_mul (hQ0 _), EuclideanSpace.norm_sq_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hs : 0 ≤ ∑ a, (WithLp.ofLp β a) ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hq := hQ0 (WithLp.ofLp β)
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [mul_nonneg hs hq]

end

theorem solution {n : ℕ} (ρ : State (Occupation (Fin n)))
    (d : Fin n × Fin 2 → ℝ) (γ : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (hγ : γ.transpose = γ)
    (h : ∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic ρ.coefficients ξ =
      Complex.exp (((-varianceForm γ ξ / 4 : ℝ) : ℂ) + Complex.I * (meanForm d ξ : ℂ))) :
    GaussianAt ρ.coefficients d γ := by
  refine ⟨⟨energy_finite ρ d γ hγ h, hγ, (husimi_fourier ρ).1, fun ξ => ?_⟩, h⟩
  refine deriv_clauses (varianceForm γ ξ) (meanForm d ξ) _ fun t => ?_
  rw [h, varianceForm_smul, meanForm_smul]
