-- Prove2me | solution 1 for BosonicLearn.eq_207
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T20:25:15.092594+00:00
-- url     : https://prove2.me/submissions/71fdc0a1-f025-4aa6-afad-af9e0ef40a43

import Mathlib
import Definitions.Def_BosonicLearn_heterodyneLaw
import Definitions.Def_BosonicLearn_IsGaussianState
import Theorems.Thm_BosonicLearn_husimi_fourier

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

open BosonicLearn

/-!
# Eq. (207): the heterodyne outcome law of a Gaussian state is `N(μ, Σ + ½I)`

Route: the Fourier transform of the Husimi density (`husimi_fourier`) and the Gaussian form of the
Weyl characteristic function (`IsGaussianState`) give the characteristic function of
`heterodyneLaw ρ`; its value at `0` gives total mass one, the bound `‖charFun‖ ≤ mass` gives
positive semidefiniteness of `Σ + ½I`, and `Measure.ext_of_charFun` identifies the law with
Mathlib's `multivariateGaussian`.
-/

noncomputable section

private lemma meanForm_interleave {n : ℕ} (μ t : Fin n ⊕ Fin n → ℝ) :
    meanForm (fun a : Fin n × Fin 2 => μ (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1))
      (fun a : Fin n × Fin 2 => if a.2 = 0 then t (Sum.inl a.1) else t (Sum.inr a.1)) =
      ∑ a, t a * μ a := by
  unfold meanForm
  rw [Fintype.sum_prod_type, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_two]
  simp

private lemma varianceForm_interleave {n : ℕ} (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (t : Fin n ⊕ Fin n → ℝ) :
    varianceForm (fun a b : Fin n × Fin 2 => 2 * S (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1)
        (if b.2 = 0 then Sum.inl b.1 else Sum.inr b.1))
      (fun a : Fin n × Fin 2 => if a.2 = 0 then t (Sum.inl a.1) else t (Sum.inr a.1)) =
      2 * ∑ a, ∑ b, t a * S a b * t b := by
  simp only [varianceForm, Fintype.sum_prod_type, Fintype.sum_sum_type, Fin.sum_univ_two]
  have h2 : ∀ a b c : ℝ, a * (2 * b) * c = 2 * (a * b * c) := fun a b c => by ring
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, Finset.mul_sum, Finset.sum_add_distrib, mul_add,
    h2]

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

end

theorem solution {n : ℕ} (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hρ : IsGaussianState ρ μ S) :
    heterodyneLaw ρ.coefficients = multivariateGaussian (WithLp.toLp 2 μ) (S + (1 / 2 : ℝ) • 1) := by
  obtain ⟨-, hQ0, hQm, hQi, hF⟩ := husimi_fourier ρ
  obtain ⟨⟨-, hsymm, -, -⟩, hchar⟩ := hρ
  -- the characteristic function of the heterodyne law
  have hcf : ∀ x : EuclideanSpace ℝ (Fin n ⊕ Fin n), charFun (heterodyneLaw ρ.coefficients) x =
      Complex.exp (((∑ a, x a * μ a : ℝ) : ℂ) * Complex.I -
        ((∑ a, ∑ b, x a * S a b * x b + (1 / 2) * ∑ a, x a ^ 2 : ℝ) : ℂ) / 2) := by
    intro x
    unfold heterodyneLaw
    rw [charFun_density _ hQ0 hQm x, hF, hchar, meanForm_interleave, varianceForm_interleave,
      Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfin : IsFiniteMeasure (heterodyneLaw ρ.coefficients) :=
    isFiniteMeasure_withDensity_ofReal (integrable_density _ hQi).2
  have hmass : (heterodyneLaw ρ.coefficients).real Set.univ = 1 := by
    have h0 := hcf 0
    rw [charFun_zero] at h0
    have : ((heterodyneLaw ρ.coefficients).real Set.univ : ℂ) = 1 := by
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
  have hS' : ∀ a b : Fin n × Fin 2,
      2 * S (if b.2 = 0 then Sum.inl b.1 else Sum.inr b.1)
          (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1) =
        2 * S (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1)
          (if b.2 = 0 then Sum.inl b.1 else Sum.inr b.1) :=
    fun a b => congr_fun (congr_fun hsymm a) b
  have hS : Sᵀ = S := by
    ext i j
    rw [Matrix.transpose_apply]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hS' (i, 0) (j, 0)
    · simpa using hS' (i, 0) (j, 1)
    · simpa using hS' (i, 1) (j, 0)
    · simpa using hS' (i, 1) (j, 1)
  have hpsd : (S + (1 / 2 : ℝ) • 1).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · show (S + (1 / 2 : ℝ) • 1)ᴴ = _
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_add,
        Matrix.transpose_smul, Matrix.transpose_one, hS]
    · have h := norm_charFun_le (μ := heterodyneLaw ρ.coefficients) (WithLp.toLp 2 x)
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
