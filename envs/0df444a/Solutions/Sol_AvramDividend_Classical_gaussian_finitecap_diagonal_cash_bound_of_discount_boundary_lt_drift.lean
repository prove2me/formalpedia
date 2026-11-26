-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_finitecap_diagonal_cash_bound_of_discount_boundary_lt_drift
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T07:03:07.936573+00:00
-- url     : https://prove2.me/submissions/0f34cf50-eeb8-4d30-bcae-28fd4f3f6f29
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_finitecap_candidate_compact_absolute_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
import Theorems.Thm_AvramDividend_Classical_gaussian_finitecap_diagonal_cash_bound_of_contDiffOn_closed_cap_neighborhood

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

private theorem derivAffine (f : ℝ → ℝ) (r a y : ℝ) :
    deriv (fun z => f (r * z + a)) y = r * deriv f (r * y + a) := by
  simpa [smul_eq_mul, deriv_comp_add_const] using
    deriv_comp_mul_left r (fun z : ℝ => f (z + a)) y

private theorem secondDeriv (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]

set_option maxHeartbeats 800000 in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hDrift : q * w 0 < X.c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  let B : ℝ := C.toReal
  have hB : 0 < B := ENNReal.toReal_pos (ne_of_gt hC) hFinite
  have hBeq : ENNReal.ofReal B = C := ENNReal.ofReal_toReal hFinite
  have hxB : x ≤ B := by
    simpa only [ENNReal.toReal_ofReal hx.le] using ENNReal.toReal_mono hFinite hxc
  have hc : 0 < X.c := lt_of_le_of_lt (mul_nonneg hq.le hw0) hDrift
  have hσ : X.σ ≠ 0 := by
    intro hσ
    apply hBV
    exact ⟨hσ, by simp [hν]⟩
  have hDiffusion : 0 < X.σ ^ 2 / 2 :=
    div_pos (sq_pos_of_ne_zero hσ) (by norm_num)
  have hInside (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) B) : ENNReal.ofReal y < C := by
    rw [← hBeq]
    exact (ENNReal.ofReal_lt_ofReal_iff hB).2 hy.2
  have hSmooth : ContDiffOn ℝ 2 w (Ioo 0 B) :=
    hw_smooth.mono fun y hy => ⟨hy.1, hInside y hy⟩
  have hCont : ContinuousOn w (Icc 0 B) :=
    hw_cont.mono fun _ hy => hy.1
  obtain ⟨M, hM, hBound⟩ :=
    avram_a22_original_finitecap_candidate_compact_absolute_bound w B hB.le hCont
  have hSlopeFloor := avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
    C hC w hw_cont (hw_smooth.of_le (by norm_num)) hw_grad B hB.le hBeq.le
  have hWNonneg (y : ℝ) (hy : y ∈ Icc (0 : ℝ) B) : 0 ≤ w y :=
    (add_nonneg hw0 hy.1).trans (hSlopeFloor y hy)

  let K := q * M / (X.σ ^ 2 / 2)
  have hK : 0 ≤ K := div_nonneg (mul_nonneg hq.le hM) hDiffusion.le
  have hSecond (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) B) : iteratedDeriv 2 w y ≤ K := by
    have hGenerator : X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
        X.c * deriv w y - q * w y ≤ 0 := by
      simpa [SpectrallyNegativeLevy.generator, hν] using
        (hw_gen y hy.1 (hInside y hy)).2
    have hDriftTerm : 0 ≤ X.c * deriv w y :=
      mul_nonneg hc.le ((by norm_num : (0 : ℝ) ≤ 1).trans (hw_grad y hy.1 (hInside y hy)))
    have hWUpper := mul_le_mul_of_nonneg_left
      ((le_abs_self (w y)).trans (hBound y hy.1.le hy.2.le)) hq.le
    apply (le_div_iff₀ hDiffusion).2
    nlinarith only [hGenerator, hDriftTerm, hWUpper]

  have hDiffFirst : ContDiffOn ℝ 1 (deriv w) (Ioo 0 B) :=
    hSmooth.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hAdjusted (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) B) :
      HasDerivAt (fun z : ℝ => deriv w z - K * z) (iteratedDeriv 2 w y - K) y := by
    have hd := (hDiffFirst.differentiableOn (by norm_num) y hy).differentiableAt
      (Ioo_mem_nhds hy.1 hy.2)
    have hm : HasDerivAt (deriv w) (iteratedDeriv 2 w y) y := by
      rw [secondDeriv]
      exact hd.hasDerivAt
    have hLinear : HasDerivAt (fun z : ℝ => K * z) K y :=
      hasDerivAt_const_mul K
    first
    | exact hm.fun_sub hLinear
    | exact hm.sub hLinear
  have hAdjCont : ContinuousOn (fun z : ℝ => deriv w z - K * z) (Ioo 0 B) :=
    hDiffFirst.continuousOn.sub (continuous_const.mul continuous_id).continuousOn
  have hDecreasing : AntitoneOn (fun z : ℝ => deriv w z - K * z) (Ioo 0 B) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo (0 : ℝ) B) hAdjCont
    · rw [isOpen_Ioo.interior_eq]
      exact fun y hy => (hAdjusted y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' : y ∈ Ioo (0 : ℝ) B := by simpa only [isOpen_Ioo.interior_eq] using hy
      rw [(hAdjusted y hy').deriv]
      exact sub_nonpos.mpr (hSecond y hy')
  have hSlope (a p : ℝ) (ha : 0 < a) (hap : a ≤ p) (hp : p < B) :
      deriv w p ≤ (w a - w 0) / a + K * B := by
    have hCa : ContinuousOn w (Icc 0 a) := hw_cont.mono fun _ hy => hy.1
    have hDa : DifferentiableOn ℝ w (Ioo 0 a) :=
      (hSmooth.differentiableOn (by norm_num)).mono fun _ hy =>
        ⟨hy.1, lt_trans hy.2 (lt_of_le_of_lt hap hp)⟩
    obtain ⟨z, hz, heq⟩ := exists_deriv_eq_slope w ha hCa hDa
    have hzp := le_trans hz.2.le hap
    have hdec := hDecreasing
      (show z ∈ Ioo 0 B from ⟨hz.1, lt_of_le_of_lt hzp hp⟩)
      (show p ∈ Ioo 0 B from ⟨lt_of_lt_of_le ha hap, hp⟩) hzp
    change deriv w p - K * p ≤ deriv w z - K * z at hdec
    rw [sub_zero] at heq
    linarith only [hdec, heq, mul_le_mul_of_nonneg_left hp.le hK, mul_nonneg hK hz.1.le]

  -- Compress the closed reserve interval into its own interior before smoothing is needed.
  let ε : ℕ → ℝ := fun j => (1 / ((j : ℝ) + 1)) / 2
  let r : ℕ → ℝ := fun j => 1 - ε j
  let a : ℕ → ℝ := fun j => ε j * B / 2
  let p : ℕ → ℝ → ℝ := fun j y => r j * y + a j
  let charge : ℕ → ℝ := fun j => (2 / B) * (w (a j) - w 0) + ε j * K * B
  let A : ℕ → ℝ := fun j => (X.c / q) * charge j
  let v : ℕ → ℝ → ℝ := fun j y => w (p j y) / r j + A j
  have hePos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have heHalf (j : ℕ) : ε j ≤ 1 / 2 := by
    have hd : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) + 1)).2
      have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
      linarith
    dsimp [ε]
    linarith
  have hrPos (j : ℕ) : 0 < r j := by dsimp [r]; linarith only [heHalf j]
  have hrLe (j : ℕ) : r j ≤ 1 := by dsimp [r]; linarith only [hePos j]
  have haPos (j : ℕ) : 0 < a j := by dsimp [a]; positivity
  have hAtB (j : ℕ) : r j * B + a j = B - a j := by dsimp [r, a]; ring
  have hpLo (j : ℕ) (y : ℝ) (hy : 0 ≤ y) : a j ≤ p j y := by
    dsimp [p]
    linarith only [mul_nonneg (hrPos j).le hy]
  have hpHi (j : ℕ) (y : ℝ) (hy : y ≤ B) : p j y < B := by
    dsimp [p]
    linarith only [mul_le_mul_of_nonneg_left hy (hrPos j).le, hAtB j, haPos j]
  have hpIn (j : ℕ) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) B) : p j y ∈ Ioo 0 B :=
    ⟨lt_of_lt_of_le (haPos j) (hpLo j y hy.1), hpHi j y hy.2⟩
  have haIn (j : ℕ) : a j ∈ Icc (0 : ℝ) B :=
    ⟨(haPos j).le, by simpa [p] using (hpHi j 0 hB.le).le⟩
  have hChargeNN (j : ℕ) : 0 ≤ charge j := by
    have hwA : 0 ≤ w (a j) - w 0 := by
      linarith only [hSlopeFloor (a j) (haIn j), haPos j]
    exact add_nonneg (mul_nonneg (by positivity) hwA)
      (mul_nonneg (mul_nonneg (hePos j).le hK) hB.le)
  have hANonneg (j : ℕ) : 0 ≤ A j := mul_nonneg (div_nonneg hc.le hq.le) (hChargeNN j)

  have hMaps (j : ℕ) :
      MapsTo (p j) (Ioo (-(a j / 2)) (B + a j / 2)) (Ioo 0 B) := by
    intro y hy
    have hlo := mul_lt_mul_of_pos_left hy.1 (hrPos j)
    have hhi := mul_lt_mul_of_pos_left hy.2 (hrPos j)
    have ha := mul_le_mul_of_nonneg_right (hrLe j) (by positivity : 0 ≤ a j / 2)
    constructor <;> dsimp [p]
    · nlinarith only [hlo, ha, haPos j]
    · nlinarith only [hhi, ha, hAtB j, haPos j]
  have hVSmooth (j : ℕ) :
      ContDiffOn ℝ 2 (v j) (Ioo (-(a j / 2)) (B + a j / 2)) := by
    have hpSmooth : ContDiff ℝ 2 (p j) :=
      (contDiff_const.mul contDiff_id).add contDiff_const
    exact ((hSmooth.comp hpSmooth.contDiffOn (hMaps j)).div_const (r j)).add contDiffOn_const
  have hVDeriv (j : ℕ) : deriv (v j) = fun y => deriv w (p j y) := by
    funext y
    change deriv (fun z => w (r j * z + a j) / r j + A j) y = deriv w (p j y)
    rw [deriv_add_const, deriv_div_const, derivAffine]
    exact mul_div_cancel_left₀ _ (hrPos j).ne'
  have hVSecond (j : ℕ) (y : ℝ) :
      iteratedDeriv 2 (v j) y = r j * iteratedDeriv 2 w (p j y) := by
    rw [secondDeriv, hVDeriv j, secondDeriv]
    exact derivAffine (deriv w) (r j) (a j) y
  have hVGen (j : ℕ) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) B) :
      X.generator (v j) y - q * v j y ≤ 0 := by
    have hyIn := hpIn j y hy
    have hBase : X.σ ^ 2 / 2 * iteratedDeriv 2 w (p j y) +
        X.c * deriv w (p j y) - q * w (p j y) ≤ 0 := by
      simpa [SpectrallyNegativeLevy.generator, hν] using
        (hw_gen (p j y) hyIn.1 (hInside (p j y) hyIn)).2
    have hBaseScaled := mul_nonpos_of_nonneg_of_nonpos (hrPos j).le hBase
    have hSlopeScaled := mul_le_mul_of_nonneg_left
      (hSlope (a j) (p j y) (haPos j) (hpLo j y hy.1) hyIn.2) (hePos j).le
    have hSlopeIdentity :
        ε j * ((w (a j) - w 0) / a j + K * B) = charge j := by
      dsimp only [a, charge]
      field_simp [(hePos j).ne', hB.ne'] <;> ring
    rw [hSlopeIdentity] at hSlopeScaled
    have hDriftError := mul_le_mul_of_nonneg_left hSlopeScaled hc.le
    have hWpos := hWNonneg (p j y) ⟨hyIn.1.le, hyIn.2.le⟩
    have hrSquare : r j * r j ≤ 1 := by
      simpa using mul_le_mul (hrLe j) (hrLe j) (hrPos j).le (show (0 : ℝ) ≤ 1 by norm_num)
    have hDiscountWeight : r j * w (p j y) ≤ w (p j y) / r j := by
      apply (le_div_iff₀ (hrPos j)).2
      nlinarith only [mul_le_mul_of_nonneg_right hrSquare hWpos]
    have hDiscount := mul_le_mul_of_nonneg_left hDiscountWeight hq.le
    have hCorrection : q * A j = X.c * charge j := by
      dsimp only [A]
      field_simp [hq.ne'] <;> ring
    have hDriftSplit : X.c * deriv w (p j y) =
        r j * (X.c * deriv w (p j y)) + X.c * (ε j * deriv w (p j y)) := by
      dsimp only [r]
      ring
    have hGeneratorV : X.generator (v j) y =
        X.σ ^ 2 / 2 * (r j * iteratedDeriv 2 w (p j y)) + X.c * deriv w (p j y) := by
      simp [SpectrallyNegativeLevy.generator, hν, hVSecond, hVDeriv]
    rw [hGeneratorV]
    change _ - q * (w (p j y) / r j + A j) ≤ 0
    nlinarith only [hBaseScaled, hDriftError, hDiscount, hCorrection, hDriftSplit]

  have hBudget (j : ℕ) :
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (v j x) := by
    apply gaussian_finitecap_diagonal_cash_bound_of_contDiffOn_closed_cap_neighborhood
      X hX hBV hν hc q hq (v j) C hC hFinite (-(a j / 2)) (B + a j / 2)
      (by linarith only [haPos j]) (by change B < B + a j / 2; linarith only [haPos j])
      (hVSmooth j) _ _ _ x hx hxc D hD n hn
    · intro y hy
      change 0 ≤ w (p j y) / r j + A j
      have hyIn := hpIn j y hy
      exact add_nonneg
        (div_nonneg (hWNonneg (p j y) ⟨hyIn.1.le, hyIn.2.le⟩) (hrPos j).le)
        (hANonneg j)
    · exact hVGen j
    · intro y hy
      rw [hVDeriv j]
      have hyIn := hpIn j y hy
      exact hw_grad (p j y) hyIn.1 (hInside _ hyIn)

  have heLim : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const (2 : ℝ))
  have haLim : Tendsto a atTop (𝓝 0) := by
    simpa [a] using ((heLim.mul_const B).div_const (2 : ℝ))
  have hrLim : Tendsto r atTop (𝓝 1) := by
    simpa [r] using ((tendsto_const_nhds (x := (1 : ℝ))).sub heLim)
  have hpxLim : Tendsto (fun j => p j x) atTop (𝓝 x) := by
    simpa [p] using (hrLim.mul_const x).add haLim
  have hwa : Tendsto (fun j => w (a j)) atTop (𝓝 (w 0)) :=
    (hw_cont 0 (by simp)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨haLim, Filter.Eventually.of_forall fun j => (haPos j).le⟩)
  have hwpx : Tendsto (fun j => w (p j x)) atTop (𝓝 (w x)) :=
    (hw_cont x hx.le).tendsto.comp
      (tendsto_nhdsWithin_iff.2
        ⟨hpxLim, Filter.Eventually.of_forall fun j => (lt_of_lt_of_le (haPos j) (hpLo j x hx.le)).le⟩)
  have hChargeLim : Tendsto charge atTop (𝓝 0) := by
    simpa [charge] using
      (((hwa.sub (tendsto_const_nhds (x := w 0))).const_mul (2 / B)).add
        ((heLim.mul_const K).mul_const B))
  have hALim : Tendsto A atTop (𝓝 0) := by
    simpa [A] using hChargeLim.const_mul (X.c / q)
  have hVLim : Tendsto (fun j => v j x) atTop (𝓝 (w x)) := by
    simpa [v] using ((hwpx.div hrLim one_ne_zero).add hALim)
  exact ge_of_tendsto' ((ENNReal.continuous_ofReal.tendsto (w x)).comp hVLim) hBudget
