-- Prove2me | solution 1 for AzumaWeightedSums.Multiplicative.weighted_sum_limsup_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:42:56.332217+00:00
-- url     : https://prove2.me/submissions/541795f0-5d70-4315-ad2d-35e67b8f6d5b

import Mathlib
import Definitions.Def_AzumaWeightedSums_Multiplicative_IsMultiplicativeSystem
import Definitions.Def_AzumaWeightedSums_Multiplicative_WeightedSums

set_option autoImplicit false

namespace AzumaExpSeriesAux

open MeasureTheory AzumaWeightedSums.Multiplicative

lemma exp_mul_le_cosh_add {c y : ℝ} (hy : |y| ≤ 1) :
    Real.exp (c * y) ≤ y * Real.sinh c + Real.cosh c := by
  have hyl : -1 ≤ y := (abs_le.mp hy).1
  have hyu : y ≤ 1 := (abs_le.mp hy).2
  have key : c * y = ((1 + y) / 2) * c + ((1 - y) / 2) * (-c) := by ring
  have hc := convexOn_exp.2 (Set.mem_univ c) (Set.mem_univ (-c))
    (show (0:ℝ) ≤ (1 + y) / 2 by linarith) (show (0:ℝ) ≤ (1 - y) / 2 by linarith)
    (by ring)
  simp only [smul_eq_mul] at hc
  rw [key]
  refine hc.trans (le_of_eq ?_)
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

lemma abs_sinh_cosh_le {c y : ℝ} (hy : |y| ≤ 1) :
    |y * Real.sinh c + Real.cosh c| ≤ Real.cosh c + |Real.sinh c| := by
  calc |y * Real.sinh c + Real.cosh c| ≤ |y * Real.sinh c| + |Real.cosh c| := abs_add_le _ _
    _ ≤ Real.cosh c + |Real.sinh c| := by
        rw [abs_of_pos (Real.cosh_pos c), abs_mul]
        have : |y| * |Real.sinh c| ≤ 1 * |Real.sinh c| :=
          mul_le_mul_of_nonneg_right hy (abs_nonneg _)
        linarith

lemma ae_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x : ℕ → Ω → ℝ} (hM : IsMultiplicativeSystem μ x) :
    ∀ᵐ ω ∂μ, ∀ n, 1 ≤ n → |x n ω| ≤ 1 := by
  rw [ae_all_iff]; intro n
  by_cases hn : 1 ≤ n
  · filter_upwards [hM.2.1 n hn] with ω h _ using h
  · exact Filter.Eventually.of_forall (fun ω h => absurd h hn)

lemma integrable_prod_x {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x : ℕ → Ω → ℝ} (hM : IsMultiplicativeSystem μ x) (t : Finset ℕ) (ht : ∀ i ∈ t, 1 ≤ i) :
    Integrable (fun ω => ∏ i ∈ t, x i ω) μ := by
  have hmeas : Measurable (fun ω => ∏ i ∈ t, x i ω) :=
    Finset.measurable_prod t (fun i hi => hM.1 i (ht i hi))
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
  filter_upwards [ae_bound hM] with ω hω
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i hi => hω i (ht i hi))

lemma integral_prod_cosh {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x : ℕ → Ω → ℝ} (hM : IsMultiplicativeSystem μ x) (I : Finset ℕ) (hI : ∀ i ∈ I, 1 ≤ i)
    (c : ℕ → ℝ) :
    ∫ ω, ∏ i ∈ I, (x i ω * Real.sinh (c i) + Real.cosh (c i)) ∂μ = ∏ i ∈ I, Real.cosh (c i) := by
  simp_rw [Finset.prod_add, Finset.prod_mul_distrib]
  rw [integral_finset_sum]
  · rw [Finset.sum_eq_single ∅]
    · simp
    · intro t ht hne
      rw [integral_mul_const, integral_mul_const,
        hM.2.2 t (Finset.nonempty_iff_ne_empty.2 hne)
          (fun i hi => hI i (Finset.mem_powerset.1 ht hi))]
      simp
    · intro h; exact absurd (Finset.empty_mem_powerset I) h
  · intro t ht
    exact ((integrable_prod_x hM t (fun i hi => hI i (Finset.mem_powerset.1 ht hi))).mul_const
      _).mul_const _

lemma measurable_weightedSum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {x : ℕ → Ω → ℝ} (hM : IsMultiplicativeSystem μ x)
    (a : ℕ → ℕ → ℝ) (n : ℕ) : Measurable (weightedSum a x n) := by
  show Measurable (fun ω => ∑ k ∈ Finset.Icc 1 n, a n k * x k ω)
  exact Finset.measurable_sum _ (fun k hk => (hM.1 k (Finset.mem_Icc.1 hk).1).const_mul _)

lemma mgf_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x : ℕ → Ω → ℝ} (hM : IsMultiplicativeSystem μ x) (a : ℕ → ℕ → ℝ) (n : ℕ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * weightedSum a x n ω)) μ ∧
    ∫ ω, Real.exp (t * weightedSum a x n ω) ∂μ ≤ Real.exp (t ^ 2 * (weightNorm a n) ^ 2 / 2) := by
  have hI : ∀ i ∈ Finset.Icc 1 n, 1 ≤ i := fun i hi => (Finset.mem_Icc.1 hi).1
  set c : ℕ → ℝ := fun k => t * a n k with hc
  set g : Ω → ℝ := fun ω => ∏ i ∈ Finset.Icc 1 n, (x i ω * Real.sinh (c i) + Real.cosh (c i))
    with hg
  have hpt : ∀ᵐ ω ∂μ, Real.exp (t * weightedSum a x n ω) ≤ g ω := by
    filter_upwards [ae_bound hM] with ω hω
    have : t * weightedSum a x n ω = ∑ i ∈ Finset.Icc 1 n, c i * x i ω := by
      simp only [weightedSum, Finset.mul_sum, hc]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [this, Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le)
      (fun i hi => exp_mul_le_cosh_add (hω i (hI i hi)))
  have hg_meas : Measurable g :=
    Finset.measurable_prod _ (fun i hi => ((hM.1 i (hI i hi)).mul_const _).add_const _)
  have hg_int : Integrable g μ := by
    refine Integrable.of_bound hg_meas.aestronglyMeasurable
      (∏ i ∈ Finset.Icc 1 n, (Real.cosh (c i) + |Real.sinh (c i)|)) ?_
    filter_upwards [ae_bound hM] with ω hω
    rw [Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _)
      (fun i hi => abs_sinh_cosh_le (hω i (hI i hi)))
  have hmeas : Measurable (fun ω => Real.exp (t * weightedSum a x n ω)) :=
    Real.measurable_exp.comp (measurable_const.mul (measurable_weightedSum hM a n))
  have hlhs : Integrable (fun ω => Real.exp (t * weightedSum a x n ω)) μ := by
    refine Integrable.mono' hg_int hmeas.aestronglyMeasurable ?_
    filter_upwards [hpt] with ω h
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact h
  refine ⟨hlhs, ?_⟩
  calc ∫ ω, Real.exp (t * weightedSum a x n ω) ∂μ ≤ ∫ ω, g ω ∂μ := integral_mono_ae hlhs hg_int hpt
    _ = ∏ i ∈ Finset.Icc 1 n, Real.cosh (c i) := integral_prod_cosh hM _ hI c
    _ ≤ ∏ i ∈ Finset.Icc 1 n, Real.exp (c i ^ 2 / 2) :=
        Finset.prod_le_prod (fun i _ => (Real.cosh_pos _).le)
          (fun i _ => Real.cosh_le_exp_half_sq _)
    _ = Real.exp (t ^ 2 * (weightNorm a n) ^ 2 / 2) := by
        rw [← Real.exp_sum, weightNorm,
          Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)), Finset.mul_sum,
          Finset.sum_div]
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp only [hc]
        ring

lemma ae_summable_of_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (F : ℕ → Ω → ℝ) (g : ℕ → ℝ)
    (h0 : ∀ n ω, 0 ≤ F n ω) (hm : ∀ n, Measurable (F n)) (hi : ∀ n, Integrable (F n) μ)
    (hle : ∀ n, ∫ ω, F n ω ∂μ ≤ g n) (hg : Summable g) :
    ∀ᵐ ω ∂μ, Summable (fun n => F n ω) := by
  have hg0 : ∀ n, 0 ≤ g n := fun n => (integral_nonneg (h0 n)).trans (hle n)
  have hlin : ∫⁻ ω, ∑' n, ENNReal.ofReal (F n ω) ∂μ < ⊤ := by
    rw [lintegral_tsum (fun n => (hm n).ennreal_ofReal.aemeasurable)]
    calc ∑' n, ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ = ∑' n, ENNReal.ofReal (∫ ω, F n ω ∂μ) := by
          congr 1; ext n
          rw [ofReal_integral_eq_lintegral_ofReal (hi n) (Filter.Eventually.of_forall (h0 n))]
      _ ≤ ∑' n, ENNReal.ofReal (g n) :=
          ENNReal.tsum_le_tsum (fun n => ENNReal.ofReal_le_ofReal (hle n))
      _ = ENNReal.ofReal (∑' n, g n) := (ENNReal.ofReal_tsum_of_nonneg hg0 hg).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hae := ae_lt_top (Measurable.ennreal_tsum (fun n => (hm n).ennreal_ofReal)) hlin.ne
  filter_upwards [hae] with ω hω
  exact (ENNReal.summable_toReal hω.ne).congr (fun n => ENNReal.toReal_ofReal (h0 n ω))

end AzumaExpSeriesAux

open MeasureTheory AzumaWeightedSums.Multiplicative in
theorem AzumaExpSeriesAux.exp_series {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ℕ → Ω → ℝ) (hM : IsMultiplicativeSystem μ x)
    (a : ℕ → ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, Summable (fun n : ℕ =>
      if 1 ≤ n then
        Real.exp
          (Real.sqrt ((2 * Real.log (n : ℝ)) / (weightNorm a n) ^ 2) *
            |weightedSum a x n ω| - (2 + ε) * Real.log (n : ℝ))
      else 0) := by
  have key : ∀ n : ℕ, 1 ≤ n →
      Measurable (fun ω => Real.exp (Real.sqrt ((2 * Real.log (n : ℝ)) / (weightNorm a n) ^ 2) *
            |weightedSum a x n ω| - (2 + ε) * Real.log (n : ℝ))) ∧
      Integrable (fun ω => Real.exp (Real.sqrt ((2 * Real.log (n : ℝ)) / (weightNorm a n) ^ 2) *
            |weightedSum a x n ω| - (2 + ε) * Real.log (n : ℝ))) μ ∧
      ∫ ω, Real.exp (Real.sqrt ((2 * Real.log (n : ℝ)) / (weightNorm a n) ^ 2) *
            |weightedSum a x n ω| - (2 + ε) * Real.log (n : ℝ)) ∂μ ≤
        2 * (n : ℝ) ^ (-(1 + ε)) := by
    intro n hn
    set s := Real.sqrt ((2 * Real.log (n : ℝ)) / (weightNorm a n) ^ 2) with hs
    set L := (2 + ε) * Real.log (n : ℝ) with hL
    have hTm := AzumaExpSeriesAux.measurable_weightedSum hM a n
    have hmeas : Measurable (fun ω => Real.exp (s * |weightedSum a x n ω| - L)) := by
      fun_prop
    have h1 := AzumaExpSeriesAux.mgf_bound hM a n s
    have h2 := AzumaExpSeriesAux.mgf_bound hM a n (-s)
    set G : Ω → ℝ := fun ω => Real.exp (-L) *
      (Real.exp (s * weightedSum a x n ω) + Real.exp ((-s) * weightedSum a x n ω)) with hG
    have hGint : Integrable G μ := (h1.1.add h2.1).const_mul _
    have hpt : ∀ ω, Real.exp (s * |weightedSum a x n ω| - L) ≤ G ω := by
      intro ω
      have h1 : Real.exp (s * |weightedSum a x n ω|) ≤
          Real.exp (s * weightedSum a x n ω) + Real.exp ((-s) * weightedSum a x n ω) := by
        rcases abs_cases (weightedSum a x n ω) with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; linarith [Real.exp_pos ((-s) * weightedSum a x n ω)]
        · rw [h, show s * -weightedSum a x n ω = (-s) * weightedSum a x n ω by ring]
          linarith [Real.exp_pos (s * weightedSum a x n ω)]
      rw [show s * |weightedSum a x n ω| - L = -L + s * |weightedSum a x n ω| by ring,
        Real.exp_add]
      exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    have hint : Integrable (fun ω => Real.exp (s * |weightedSum a x n ω| - L)) μ := by
      refine Integrable.mono' hGint hmeas.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
      intro ω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hpt ω
    refine ⟨hmeas, hint, ?_⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    have hs2 : s ^ 2 * (weightNorm a n) ^ 2 ≤ 2 * Real.log n := by
      rw [hs, Real.sq_sqrt (div_nonneg (by linarith) (sq_nonneg _))]
      rcases eq_or_ne ((weightNorm a n) ^ 2) 0 with h | h
      · rw [h, mul_zero]; linarith
      · rw [div_mul_cancel₀ _ h]
    have hE : Real.exp (s ^ 2 * (weightNorm a n) ^ 2 / 2) ≤ (n : ℝ) := by
      calc Real.exp (s ^ 2 * (weightNorm a n) ^ 2 / 2) ≤ Real.exp (Real.log n) :=
            Real.exp_le_exp.2 (by linarith)
        _ = n := Real.exp_log hnpos
    have h2' : ∫ ω, Real.exp ((-s) * weightedSum a x n ω) ∂μ ≤
        Real.exp (s ^ 2 * (weightNorm a n) ^ 2 / 2) := by
      have := h2.2; rwa [neg_sq] at this
    calc ∫ ω, Real.exp (s * |weightedSum a x n ω| - L) ∂μ ≤ ∫ ω, G ω ∂μ :=
          integral_mono hint hGint hpt
      _ = Real.exp (-L) * (∫ ω, Real.exp (s * weightedSum a x n ω) ∂μ +
            ∫ ω, Real.exp ((-s) * weightedSum a x n ω) ∂μ) := by
          rw [hG, integral_const_mul, integral_add h1.1 h2.1]
      _ ≤ Real.exp (-L) * ((n : ℝ) + n) := by
          gcongr
          · exact h1.2.trans hE
          · exact h2'.trans hE
      _ = 2 * (n : ℝ) ^ (-(1 + ε)) := by
          rw [Real.rpow_def_of_pos hnpos]
          have : Real.exp (Real.log n * -(1 + ε)) = Real.exp (-L) * Real.exp (Real.log n) := by
            rw [← Real.exp_add]; congr 1; rw [hL]; ring
          rw [this, Real.exp_log hnpos]; ring
  refine AzumaExpSeriesAux.ae_summable_of_integral_le (μ := μ)
    (fun n ω => if 1 ≤ n then
        Real.exp
          (Real.sqrt ((2 * Real.log (n : ℝ)) / (weightNorm a n) ^ 2) *
            |weightedSum a x n ω| - (2 + ε) * Real.log (n : ℝ))
      else 0)
    (fun n => 2 * (n : ℝ) ^ (-(1 + ε))) ?_ ?_ ?_ ?_ ?_
  · intro n ω
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  · intro n
    by_cases hn : 1 ≤ n
    · simpa only [if_pos hn] using (key n hn).1
    · simp only [if_neg hn]; exact measurable_const
  · intro n
    by_cases hn : 1 ≤ n
    · simpa only [if_pos hn] using (key n hn).2.1
    · simp only [if_neg hn]; exact integrable_const _
  · intro n
    by_cases hn : 1 ≤ n
    · simpa only [if_pos hn] using (key n hn).2.2
    · have hn0 : n = 0 := by omega
      subst hn0
      simp only [if_neg hn, integral_zero, Nat.cast_zero]
      rw [Real.zero_rpow (by linarith)]; norm_num
  · exact (Real.summable_nat_rpow.2 (by linarith)).mul_left 2


open MeasureTheory Filter AzumaWeightedSums.Multiplicative in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ℕ → Ω → ℝ) (hM : IsMultiplicativeSystem μ x)
    (a : ℕ → ℕ → ℝ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
        |weightedSum a x n ω| ≤
          (1 + ε) * Real.sqrt (2 * (weightNorm a n) ^ 2 * Real.log (n : ℝ)) := by
  intro ε hε
  have hS := AzumaExpSeriesAux.exp_series μ x hM a (2 * ε) (by linarith)
  filter_upwards [hS] with ω hω
  have ht := hω.tendsto_atTop_zero
  filter_upwards [ht.eventually (gt_mem_nhds one_pos), eventually_ge_atTop 2] with n hn hn2
  have h1 : 1 ≤ n := by omega
  rw [if_pos h1] at hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  set W := weightNorm a n with hW
  set T := weightedSum a x n ω with hT
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hRHS : 0 ≤ (1 + ε) * Real.sqrt (2 * W ^ 2 * Real.log (n : ℝ)) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  rcases hW0.lt_or_eq with hWp | hWz
  · set r := Real.sqrt (2 * Real.log (n : ℝ)) with hr
    have hrp : 0 < r := Real.sqrt_pos.2 (by linarith)
    have hr2 : r ^ 2 = 2 * Real.log (n : ℝ) := Real.sq_sqrt (by linarith)
    have hs : Real.sqrt ((2 * Real.log (n : ℝ)) / W ^ 2) = r / W := by
      rw [← hr2, ← div_pow, Real.sqrt_sq (div_pos hrp hWp).le]
    have hsq : Real.sqrt (2 * W ^ 2 * Real.log (n : ℝ)) = W * r := by
      rw [show 2 * W ^ 2 * Real.log (n : ℝ) = (W * r) ^ 2 by rw [mul_pow, hr2]; ring]
      exact Real.sqrt_sq (mul_pos hWp hrp).le
    rw [hs] at hn
    rw [hsq]
    have hexp : r / W * |T| - (2 + 2 * ε) * Real.log (n : ℝ) < 0 := by
      by_contra hc
      push Not at hc
      have := Real.add_one_le_exp (r / W * |T| - (2 + 2 * ε) * Real.log (n : ℝ))
      linarith
    have hkey : r / W * |T| < (1 + ε) * r ^ 2 := by rw [hr2]; linarith
    have hkey2 : r * |T| < (1 + ε) * r ^ 2 * W := by
      have := mul_lt_mul_of_pos_right hkey hWp
      have e : r / W * |T| * W = r * |T| := by field_simp
      rwa [e] at this
    have : r * |T| ≤ r * ((1 + ε) * (W * r)) := by nlinarith
    exact le_of_mul_le_mul_left this hrp
  · have hsum0 : ∑ k ∈ Finset.Icc 1 n, (a n k) ^ 2 = 0 := by
      have h := hWz.symm
      rw [hW, weightNorm, Real.sqrt_eq_zero'] at h
      exact le_antisymm h (Finset.sum_nonneg (fun k _ => sq_nonneg _))
    have hak : ∀ k ∈ Finset.Icc 1 n, a n k = 0 := by
      intro k hk
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (a n k))).1 hsum0 k hk
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have hT0 : T = 0 := by
      rw [hT, weightedSum]
      exact Finset.sum_eq_zero (fun k hk => by rw [hak k hk, zero_mul])
    rw [hT0, abs_zero]
    exact hRHS
