-- Prove2me | solution 1 for BurkholderDFI.SquareFnLp.lemma_3_1_b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:00:42.879113+00:00
-- url     : https://prove2.me/submissions/dc8d7da2-d139-47a5-bd2a-29ac3a02091c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Theorems.Thm_BurkholderDFI_SquareFnLp_lemma_3_1_a
import Theorems.Thm_BurkholderDFI_SquareFnLp_eq_1_3

set_option autoImplicit false

namespace BurkholderDFI.SquareFnLp.Lemma31bProof

open MeasureTheory ProbabilityTheory Filter Topology BurkholderDFI.SquareFnLp
open scoped ENNReal NNReal

variable {Ω : Type*}

theorem measurable_dseq [MeasurableSpace Ω] {g : ℕ → Ω → ℝ} (hg : ∀ k, Measurable (g k))
    (k : ℕ) : Measurable (dseq g k) := by
  by_cases h0 : k = 0
  · subst h0
    have : dseq g 0 = fun _ => (0 : ℝ) := by funext ω; simp [dseq]
    rw [this]
    exact measurable_const
  by_cases h1 : k = 1
  · subst h1
    have : dseq g 1 = g 1 := by funext ω; simp [dseq]
    rw [this]
    exact hg 1
  · have : dseq g k = fun ω => g k ω - g (k - 1) ω := by funext ω; simp [dseq, h0, h1]
    rw [this]
    exact (hg k).sub (hg (k - 1))

theorem measurable_sqFnN [MeasurableSpace Ω] {g : ℕ → Ω → ℝ} (hg : ∀ k, Measurable (g k))
    (n : ℕ) : Measurable (sqFnN g n) := by
  unfold sqFnN
  refine ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp ?_)
  exact Finset.measurable_sum _ fun k _ => (measurable_dseq hg k).pow_const 2

theorem measurable_maxFnN [MeasurableSpace Ω] {g : ℕ → Ω → ℝ} (hg : ∀ k, Measurable (g k))
    (n : ℕ) : Measurable (maxFnN g n) := by
  unfold maxFnN
  exact Measurable.iSup fun k => Measurable.iSup fun _ => ENNReal.measurable_ofReal.comp
    (hg k).abs

theorem dseq_const_mul (g : ℕ → Ω → ℝ) (θ : ℝ) (k : ℕ) (ω : Ω) :
    dseq (fun k x => θ * g k x) k ω = θ * dseq g k ω := by
  unfold dseq
  split_ifs <;> ring

theorem sqFnN_const_mul (g : ℕ → Ω → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) (n : ℕ) (ω : Ω) :
    sqFnN (fun k x => θ * g k x) n ω = ENNReal.ofReal θ * sqFnN g n ω := by
  unfold sqFnN
  simp_rw [dseq_const_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg θ), Real.sqrt_sq hθ,
    ENNReal.ofReal_mul hθ]

theorem lpNormE_mono [MeasurableSpace Ω] (P : Measure Ω) {p : ℝ} (hp : 0 < p)
    {A B : Ω → ℝ≥0∞} (h : ∀ ω, A ω ≤ B ω) : lpNormE P p A ≤ lpNormE P p B := by
  unfold lpNormE
  exact ENNReal.rpow_le_rpow (lintegral_mono fun ω => ENNReal.rpow_le_rpow (h ω) hp.le)
    (by positivity)

theorem lpNormE_const_mul [MeasurableSpace Ω] (P : Measure Ω) {p : ℝ} (hp : 0 < p)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (A : Ω → ℝ≥0∞) :
    lpNormE P p (fun ω => c * A ω) = c * lpNormE P p A := by
  unfold lpNormE
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le hc),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- `(1 + 2/p)^{p/2} ≤ e < 3`, in the form `√(1 + 2θ²)^p ≤ 3` with `θ² = 1/p`. -/
theorem beta_rpow_le_three {p : ℝ} (hp : 0 < p) :
    Real.sqrt (1 + 2 * (Real.sqrt p)⁻¹ ^ 2) ^ p ≤ 3 := by
  have hθ2 : (Real.sqrt p)⁻¹ ^ 2 = 1 / p := by
    rw [inv_pow, Real.sq_sqrt hp.le, one_div]
  have hle : Real.sqrt (1 + 2 * (Real.sqrt p)⁻¹ ^ 2) ≤ Real.exp (1 / p) := by
    rw [hθ2]
    have h1 : 1 + 2 * (1 / p) ≤ Real.exp (1 / p) ^ 2 := by
      rw [← Real.exp_nat_mul]
      have := Real.add_one_le_exp (2 * (1 / p))
      push_cast
      linarith
    calc Real.sqrt (1 + 2 * (1 / p)) ≤ Real.sqrt (Real.exp (1 / p) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.exp (1 / p) := Real.sqrt_sq (Real.exp_pos _).le
  calc Real.sqrt (1 + 2 * (Real.sqrt p)⁻¹ ^ 2) ^ p ≤ Real.exp (1 / p) ^ p :=
        Real.rpow_le_rpow (Real.sqrt_nonneg _) hle hp.le
    _ = Real.exp 1 := by rw [← Real.exp_mul, one_div_mul_cancel hp.ne']
    _ ≤ 3 := by
      have := Real.exp_one_lt_d9
      linarith

end BurkholderDFI.SquareFnLp.Lemma31bProof

open MeasureTheory ProbabilityTheory Filter Topology BurkholderDFI.SquareFnLp
  BurkholderDFI.SquareFnLp.Lemma31bProof
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hsub : Submartingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)
    (n : ℕ) (hn : 1 ≤ n) (p q : ℝ) (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    lpNormE P p (sqFnN f n)
      ≤ ENNReal.ofReal (9 * Real.sqrt p * q) * lpNormE P p (fun ω => ENNReal.ofReal |f n ω|) := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < q := by
    have hqi : q⁻¹ = 1 - p⁻¹ := by linarith
    have : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
    exact inv_pos.mp (by rw [hqi]; linarith)
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  set θ : ℝ := (Real.sqrt p)⁻¹ with hθdef
  have hθ : 0 < θ := inv_pos.mpr hsp
  set β : ℝ := Real.sqrt (1 + 2 * θ ^ 2) with hβdef
  have hβ1 : 1 ≤ β := Real.one_le_sqrt.mpr (by nlinarith)
  have hfm : ∀ k, Measurable (f k) := fun k =>
    ((hsub.1 k).mono (ℱ.le k)).measurable
  set Y : Ω → ℝ≥0∞ := fun ω => max (sqFnN (fun k x => θ * f k x) n ω) (maxFnN f n ω)
    with hYdef
  set X : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (f n ω) with hXdef
  have hX : Measurable X := ENNReal.measurable_ofReal.comp (hfm n)
  have hY : Measurable Y :=
    (measurable_sqFnN (fun k => (hfm k).const_mul θ) n).max (measurable_maxFnN hfm n)
  -- (3.4) is the distribution inequality required by (1.3), with `α = 3`.
  have h12 : ∀ l : ℝ, 0 < l →
      ENNReal.ofReal l * P {ω | ENNReal.ofReal (β * l) < Y ω}
        ≤ ENNReal.ofReal 3 * ∫⁻ ω in {ω | ENNReal.ofReal l < Y ω}, X ω ∂P := by
    intro l hl
    rw [ENNReal.ofReal_ofNat]
    exact lemma_3_1_a hsub hnn n hn θ hθ l hl
  have h13 := eq_1_3 P X Y hX hY 3 β (by norm_num) hβ1 h12 p q hp hpq
  -- `θ S_n(f) ≤ Y`.
  have hSY : ENNReal.ofReal θ * lpNormE P p (sqFnN f n) ≤ lpNormE P p Y := by
    rw [← lpNormE_const_mul P hp0 _ ENNReal.ofReal_ne_top]
    refine lpNormE_mono P hp0 fun ω => ?_
    rw [← sqFnN_const_mul f hθ.le n ω]
    exact le_max_left _ _
  have hXabs : lpNormE P p X ≤ lpNormE P p (fun ω => ENNReal.ofReal |f n ω|) :=
    lpNormE_mono P hp0 fun ω => ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hconst : ENNReal.ofReal (Real.sqrt p) * ENNReal.ofReal (3 * β ^ p * q)
      ≤ ENNReal.ofReal (9 * Real.sqrt p * q) := by
    rw [← ENNReal.ofReal_mul hsp.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb := beta_rpow_le_three hp0
    have hb0 : 0 ≤ β ^ p := Real.rpow_nonneg (Real.sqrt_nonneg _) p
    have : Real.sqrt p * (3 * β ^ p * q) = 3 * (Real.sqrt p * q) * β ^ p := by ring
    rw [this]
    have hsq : 0 ≤ Real.sqrt p * q := mul_nonneg hsp.le hq.le
    nlinarith
  have hinv : ENNReal.ofReal (Real.sqrt p) * ENNReal.ofReal θ = 1 := by
    rw [← ENNReal.ofReal_mul hsp.le, hθdef, mul_inv_cancel₀ hsp.ne', ENNReal.ofReal_one]
  calc lpNormE P p (sqFnN f n)
      = ENNReal.ofReal (Real.sqrt p) * (ENNReal.ofReal θ * lpNormE P p (sqFnN f n)) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ ENNReal.ofReal (Real.sqrt p) * (ENNReal.ofReal (3 * β ^ p * q) * lpNormE P p X) := by
        exact mul_le_mul' le_rfl (hSY.trans h13)
    _ = (ENNReal.ofReal (Real.sqrt p) * ENNReal.ofReal (3 * β ^ p * q)) * lpNormE P p X :=
        (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal (9 * Real.sqrt p * q) * lpNormE P p (fun ω => ENNReal.ofReal |f n ω|) :=
        mul_le_mul' hconst hXabs
