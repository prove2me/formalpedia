-- Prove2me | solution 1 for BurkholderDFI.SquareFnLp.eq_3_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:02:39.938626+00:00
-- url     : https://prove2.me/submissions/4d3994bc-25d7-4d09-8473-bf8dda24a33a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Theorems.Thm_BurkholderDFI_SquareFnLp_lemma_3_1_b

set_option autoImplicit false

namespace BurkholderDFI.SquareFnLp.Eq37Proof

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

theorem lpNormE_mono [MeasurableSpace Ω] (P : Measure Ω) {p : ℝ} (hp : 0 < p)
    {A B : Ω → ℝ≥0∞} (h : ∀ ω, A ω ≤ B ω) : lpNormE P p A ≤ lpNormE P p B := by
  unfold lpNormE
  exact ENNReal.rpow_le_rpow (lintegral_mono fun ω => ENNReal.rpow_le_rpow (h ω) hp.le)
    (by positivity)

/-- Minkowski's inequality in finite-dimensional `ℓ²`. -/
theorem sqrt_sum_sub_sq_le (s : Finset ℕ) (a b : ℕ → ℝ) :
    Real.sqrt (∑ k ∈ s, (a k - b k) ^ 2)
      ≤ Real.sqrt (∑ k ∈ s, a k ^ 2) + Real.sqrt (∑ k ∈ s, b k ^ 2) := by
  have hA : Real.sqrt (∑ k ∈ s, a k ^ 2) ^ 2 = ∑ k ∈ s, a k ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hB : Real.sqrt (∑ k ∈ s, b k ^ 2) ^ 2 = ∑ k ∈ s, b k ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hA0 := Real.sqrt_nonneg (∑ k ∈ s, a k ^ 2)
  have hB0 := Real.sqrt_nonneg (∑ k ∈ s, b k ^ 2)
  have hab : -(∑ k ∈ s, a k * b k)
      ≤ Real.sqrt (∑ k ∈ s, a k ^ 2) * Real.sqrt (∑ k ∈ s, b k ^ 2) := by
    have h1 : (∑ k ∈ s, a k * b k) ^ 2
        ≤ (Real.sqrt (∑ k ∈ s, a k ^ 2) * Real.sqrt (∑ k ∈ s, b k ^ 2)) ^ 2 := by
      rw [mul_pow, hA, hB]
      exact Finset.sum_mul_sq_le_sq_mul_sq s a b
    have h2 := sq_le_sq.mp h1
    rw [abs_of_nonneg (mul_nonneg hA0 hB0)] at h2
    linarith [neg_abs_le (∑ k ∈ s, a k * b k)]
  have hexp : ∑ k ∈ s, (a k - b k) ^ 2
      = ∑ k ∈ s, a k ^ 2 + ∑ k ∈ s, b k ^ 2 - 2 * ∑ k ∈ s, a k * b k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  calc Real.sqrt (∑ k ∈ s, (a k - b k) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ k ∈ s, a k ^ 2) + Real.sqrt (∑ k ∈ s, b k ^ 2)) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [hexp, add_sq, hA, hB]
        linarith
    _ = Real.sqrt (∑ k ∈ s, a k ^ 2) + Real.sqrt (∑ k ∈ s, b k ^ 2) :=
        Real.sqrt_sq (add_nonneg hA0 hB0)

end BurkholderDFI.SquareFnLp.Eq37Proof

open MeasureTheory ProbabilityTheory Filter Topology BurkholderDFI.SquareFnLp
  BurkholderDFI.SquareFnLp.Eq37Proof
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (n : ℕ) (hn : 1 ≤ n) (p q : ℝ) (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    lpNormE P p (sqFnN f n)
      ≤ ENNReal.ofReal (18 * Real.sqrt p * q) * lpNormE P p (fun ω => ENNReal.ofReal |f n ω|) := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < q := by
    have hqi : q⁻¹ = 1 - p⁻¹ := by linarith
    have : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
    exact inv_pos.mp (by rw [hqi]; linarith)
  have hc0 : 0 ≤ 9 * Real.sqrt p * q := by positivity
  -- Krickeberg-type splitting of `f_n` into nonnegative martingales.
  set fp : Ω → ℝ := fun ω => max (f n ω) 0 with hfpdef
  set fm : Ω → ℝ := fun ω => max (-f n ω) 0 with hfmdef
  have hint := hf.integrable n
  have hfpi : Integrable fp P := hint.pos_part
  have hfmi : Integrable fm P := hint.neg_part
  set g : ℕ → Ω → ℝ := fun k => P[fp | ℱ k] with hgdef
  set h : ℕ → Ω → ℝ := fun k => P[fm | ℱ k] with hhdef
  have hg : Martingale g ℱ P := martingale_condExp fp ℱ P
  have hh : Martingale h ℱ P := martingale_condExp fm ℱ P
  have hgnn : ∀ k, 1 ≤ k → 0 ≤ᵐ[P] g k := fun k _ =>
    condExp_nonneg (Eventually.of_forall fun ω => le_max_right _ _)
  have hhnn : ∀ k, 1 ≤ k → 0 ≤ᵐ[P] h k := fun k _ =>
    condExp_nonneg (Eventually.of_forall fun ω => le_max_right _ _)
  have hSg := lemma_3_1_b hg.submartingale hgnn n hn p q hp hpq
  have hSh := lemma_3_1_b hh.submartingale hhnn n hn p q hp hpq
  have hfnm : StronglyMeasurable[ℱ n] (f n) := hf.1 n
  have hgn : g n = fp :=
    condExp_of_stronglyMeasurable (ℱ.le n)
      (hfnm.measurable.max measurable_const).stronglyMeasurable hfpi
  have hhn : h n = fm :=
    condExp_of_stronglyMeasurable (ℱ.le n)
      (hfnm.measurable.neg.max measurable_const).stronglyMeasurable hfmi
  have hgX : lpNormE P p (fun ω => ENNReal.ofReal |g n ω|)
      ≤ lpNormE P p (fun ω => ENNReal.ofReal |f n ω|) := by
    refine lpNormE_mono P hp0 fun ω => ENNReal.ofReal_le_ofReal ?_
    rw [hgn, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hhX : lpNormE P p (fun ω => ENNReal.ofReal |h n ω|)
      ≤ lpNormE P p (fun ω => ENNReal.ofReal |f n ω|) := by
    refine lpNormE_mono P hp0 fun ω => ENNReal.ofReal_le_ofReal ?_
    rw [hhn, abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  -- `f_k = g_k - h_k` almost surely for `k ≤ n`.
  have hdec : ∀ k, k ≤ n → f k =ᵐ[P] g k - h k := by
    intro k hk
    have h1 : P[f n | ℱ k] =ᵐ[P] f k := hf.condExp_ae_eq hk
    have h2 : f n = fp - fm := by
      funext ω
      simp only [Pi.sub_apply, hfpdef, hfmdef]
      exact (max_zero_sub_eq_self (f n ω)).symm
    have h3 : P[fp - fm | ℱ k] =ᵐ[P] P[fp | ℱ k] - P[fm | ℱ k] := condExp_sub hfpi hfmi (ℱ k)
    rw [h2] at h1
    exact h1.symm.trans h3
  have hall : ∀ᵐ ω ∂P, ∀ k, k ≤ n → f k ω = g k ω - h k ω := by
    rw [ae_all_iff]
    intro k
    by_cases hk : k ≤ n
    · exact (hdec k hk).mono fun ω hω _ => by simpa using hω
    · exact Eventually.of_forall fun ω hk' => absurd hk' hk
  -- Pointwise, `S_n(f) ≤ S_n(g) + S_n(h)` almost surely.
  have hpt : ∀ᵐ ω ∂P, sqFnN f n ω ≤ sqFnN g n ω + sqFnN h n ω := by
    filter_upwards [hall] with ω hω
    have hd : ∀ k ∈ Finset.Icc 1 n, dseq f k ω = dseq g k ω - dseq h k ω := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      unfold dseq
      split_ifs with h0 h1
      · ring
      · subst h1
        exact hω 1 hk.2
      · rw [hω k hk.2, hω (k - 1) (by omega)]
        ring
    unfold sqFnN
    rw [Finset.sum_congr rfl fun k hk => by rw [hd k hk],
      ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (sqrt_sum_sub_sq_le _ _ _)
  have hgm : ∀ k, Measurable (g k) := fun k =>
    (stronglyMeasurable_condExp.mono (ℱ.le k)).measurable
  have hhm : ∀ k, Measurable (h k) := fun k =>
    (stronglyMeasurable_condExp.mono (ℱ.le k)).measurable
  have hmink : lpNormE P p (sqFnN f n) ≤ lpNormE P p (sqFnN g n) + lpNormE P p (sqFnN h n) := by
    calc lpNormE P p (sqFnN f n) ≤ lpNormE P p (sqFnN g n + sqFnN h n) := by
          unfold lpNormE
          exact ENNReal.rpow_le_rpow
            (lintegral_mono_ae (hpt.mono fun ω hω => ENNReal.rpow_le_rpow hω hp0.le))
            (by positivity)
      _ ≤ lpNormE P p (sqFnN g n) + lpNormE P p (sqFnN h n) :=
          ENNReal.lintegral_Lp_add_le (measurable_sqFnN hgm n).aemeasurable
            (measurable_sqFnN hhm n).aemeasurable hp.le
  calc lpNormE P p (sqFnN f n)
      ≤ lpNormE P p (sqFnN g n) + lpNormE P p (sqFnN h n) := hmink
    _ ≤ ENNReal.ofReal (9 * Real.sqrt p * q) * lpNormE P p (fun ω => ENNReal.ofReal |g n ω|)
        + ENNReal.ofReal (9 * Real.sqrt p * q) * lpNormE P p (fun ω => ENNReal.ofReal |h n ω|) :=
        add_le_add hSg hSh
    _ ≤ ENNReal.ofReal (9 * Real.sqrt p * q) * lpNormE P p (fun ω => ENNReal.ofReal |f n ω|)
        + ENNReal.ofReal (9 * Real.sqrt p * q) * lpNormE P p (fun ω => ENNReal.ofReal |f n ω|) :=
        add_le_add (mul_le_mul' le_rfl hgX) (mul_le_mul' le_rfl hhX)
    _ = ENNReal.ofReal (18 * Real.sqrt p * q) * lpNormE P p (fun ω => ENNReal.ofReal |f n ω|) := by
        rw [← add_mul, ← ENNReal.ofReal_add hc0 hc0]
        congr 2
        ring
