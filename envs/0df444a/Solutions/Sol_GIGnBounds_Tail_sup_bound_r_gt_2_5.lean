-- Prove2me | solution 1 for GIGnBounds.Tail.sup_bound_r_gt_2_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T00:08:46.381769+00:00
-- url     : https://prove2.me/submissions/5be4f73f-c02f-48af-8805-ea391f39fa5c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting
import Theorems.Thm_GIGnBounds_Tail_theorem_10
import Theorems.Thm_GIGnBounds_Tail_lemma_5
import Theorems.Thm_GIGnBounds_Tail_lemma_6

open MeasureTheory ProbabilityTheory GIGnBounds.Tail

namespace GIGnSBAux

lemma mr {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a * b) ^ r = a ^ r * b ^ r :=
  Real.mul_rpow ha hb

/-- The numerical inequality behind "some straightforward algebra" on p. 28. -/
lemma alg (r M E : ℝ) (hr : 5 / 2 < r) (hM : 2 ≤ M) (hE : 1 ≤ E) :
    18 / 10 * (1 + 1 / (r - r / 2)) * (32 * (r + 1) / (r / 2 - 1)) ^ (r + 1) *
        (76 / 100 * M ^ r * (1032 : ℝ) ^ r * r ^ (2 * r) +
          21 / 100 * M * (516 : ℝ) ^ r * r ^ ((3 : ℝ) / 2 * r) * (E + 1)) +
      18 / 10 * (1 + 1 / (r - r / 2)) * (46 * (r + 1) / (r / 2 - 1)) ^ (r + 1) *
        (52 / 10 * (35 * M) ^ r * r ^ ((5 : ℝ) / 2 * r)) ≤
    13 * 10 ^ 3 * M * ((46 : ℝ) * 10 ^ 4) ^ r *
      (M ^ (r - 1) * r ^ ((5 : ℝ) / 2 * r) + r ^ ((3 : ℝ) / 2 * r) * E) := by
  have hr0 : 0 < r := by linarith
  have hM0 : 0 < M := by linarith
  -- the prefactor
  have hL : 18 / 10 * (1 + 1 / (r - r / 2)) ≤ 324 / 100 := by
    have : 1 / (r - r / 2) ≤ 4 / 5 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have hL0 : 0 ≤ 18 / 10 * (1 + 1 / (r - r / 2)) := by
    have : 0 < r - r / 2 := by linarith
    positivity
  -- `q = (r+1)/(r/2-1) ≤ 14`
  have hq0 : 0 ≤ (r + 1) / (r / 2 - 1) := div_nonneg (by linarith) (by linarith)
  have hq : (r + 1) / (r / 2 - 1) ≤ 14 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hP1 : (32 * (r + 1) / (r / 2 - 1)) ^ (r + 1) ≤ 448 * (448 : ℝ) ^ r := by
    have h1 : (32 * (r + 1) / (r / 2 - 1)) ^ (r + 1) ≤ (448 : ℝ) ^ (r + 1) := by
      apply Real.rpow_le_rpow (by rw [mul_div_assoc]; exact mul_nonneg (by norm_num) hq0) _
        (by linarith)
      rw [mul_div_assoc]; linarith
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 448), Real.rpow_one] at h1
    linarith
  have hP2 : (46 * (r + 1) / (r / 2 - 1)) ^ (r + 1) ≤ 644 * (644 : ℝ) ^ r := by
    have h1 : (46 * (r + 1) / (r / 2 - 1)) ^ (r + 1) ≤ (644 : ℝ) ^ (r + 1) := by
      apply Real.rpow_le_rpow (by rw [mul_div_assoc]; exact mul_nonneg (by norm_num) hq0) _
        (by linarith)
      rw [mul_div_assoc]; linarith
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 644), Real.rpow_one] at h1
    linarith
  -- rewrite powers of `r`
  have er2 : r ^ (2 * r) = (r ^ (2 : ℝ)) ^ r := Real.rpow_mul hr0.le 2 r
  have er15 : r ^ ((3 : ℝ) / 2 * r) = (r ^ ((3 : ℝ) / 2)) ^ r := Real.rpow_mul hr0.le _ r
  have er25 : r ^ ((5 : ℝ) / 2 * r) = (r ^ ((5 : ℝ) / 2)) ^ r := Real.rpow_mul hr0.le _ r
  have hMr : M * M ^ (r - 1) = M ^ r := by
    rw [← Real.rpow_one_add' hM0.le (by linarith)]; ring_nf
  set a := r ^ (2 : ℝ) with ha
  set b := r ^ ((3 : ℝ) / 2) with hb
  set c := r ^ ((5 : ℝ) / 2) with hc
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hc0 : 0 ≤ c := by positivity
  clear_value a b c
  -- `a * 462336 ≤ c * 460000`, i.e. `462336 r² ≤ 460000 r^{5/2}`
  have hac : 448 * 1032 * a ≤ 46 * 10 ^ 4 * c := by
    have hca : c = a * r ^ ((1 : ℝ) / 2) := by
      rw [hc, ha, ← Real.rpow_add hr0]; norm_num
    have hs : (3 : ℝ) / 2 ≤ r ^ ((1 : ℝ) / 2) := by
      have : ((3 : ℝ) / 2) = ((9 : ℝ) / 4) ^ ((1 : ℝ) / 2) := by
        rw [show ((9 : ℝ) / 4) = (3 / 2) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [this]
      exact Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
    rw [hca]
    have h1 := mul_le_mul_of_nonneg_left hs ha0
    generalize r ^ ((1 : ℝ) / 2) = t at h1 ⊢
    linarith
  -- the three comparisons
  have hA : (448 : ℝ) ^ r * (M ^ r * (1032 : ℝ) ^ r * a ^ r) ≤ (46 * 10 ^ 4 * M * c) ^ r := by
    have : (448 : ℝ) ^ r * (M ^ r * (1032 : ℝ) ^ r * a ^ r) = (448 * 1032 * a * M) ^ r := by
      rw [mr (by positivity) hM0.le, mr (by positivity) ha0, mr (by norm_num) (by norm_num)]
      ring
    rw [this]
    apply Real.rpow_le_rpow (by positivity) _ hr0.le
    nlinarith [mul_le_mul_of_nonneg_right hac hM0.le]
  have hB : (644 : ℝ) ^ r * (35 * M) ^ r * c ^ r ≤ (46 * 10 ^ 4 * M * c) ^ r := by
    rw [← mr (by norm_num) (by positivity), ← mr (by positivity) hc0]
    apply Real.rpow_le_rpow (by positivity) _ hr0.le
    nlinarith [mul_nonneg hM0.le hc0]
  have hC : (448 : ℝ) ^ r * (516 : ℝ) ^ r * b ^ r ≤ (46 * 10 ^ 4 * b) ^ r := by
    rw [← mr (by norm_num) (by norm_num), ← mr (by positivity) hb0]
    apply Real.rpow_le_rpow (by positivity) _ hr0.le
    nlinarith
  have hRHS : 13 * 10 ^ 3 * M * ((46 : ℝ) * 10 ^ 4) ^ r *
      (M ^ (r - 1) * r ^ ((5 : ℝ) / 2 * r) + r ^ ((3 : ℝ) / 2 * r) * E) =
      13 * 10 ^ 3 * (46 * 10 ^ 4 * M * c) ^ r + 13 * 10 ^ 3 * M * (46 * 10 ^ 4 * b) ^ r * E := by
    rw [er15, er25, mr (by positivity) hc0, mr (by positivity) hM0.le, mr (by norm_num) hb0,
      ← hMr]
    ring
  rw [hRHS, er2, er15, er25]
  -- positivity facts
  have hX : 0 ≤ (46 * 10 ^ 4 * M * c) ^ r := by positivity
  have hY : 0 ≤ (46 * 10 ^ 4 * b) ^ r := by positivity
  have h448 : 0 ≤ (448 : ℝ) ^ r := by positivity
  have h644 : 0 ≤ (644 : ℝ) ^ r := by positivity
  have hC1 : 0 ≤ 76 / 100 * M ^ r * (1032 : ℝ) ^ r * a ^ r +
      21 / 100 * M * (516 : ℝ) ^ r * b ^ r * (E + 1) := by positivity
  have hC2 : 0 ≤ 52 / 10 * (35 * M) ^ r * c ^ r := by positivity
  have hP1n : 0 ≤ (32 * (r + 1) / (r / 2 - 1)) ^ (r + 1) :=
    Real.rpow_nonneg (by rw [mul_div_assoc]; exact mul_nonneg (by norm_num) hq0) _
  have hP2n : 0 ≤ (46 * (r + 1) / (r / 2 - 1)) ^ (r + 1) :=
    Real.rpow_nonneg (by rw [mul_div_assoc]; exact mul_nonneg (by norm_num) hq0) _
  set L := 18 / 10 * (1 + 1 / (r - r / 2))
  have step1 : L * (32 * (r + 1) / (r / 2 - 1)) ^ (r + 1) *
      (76 / 100 * M ^ r * (1032 : ℝ) ^ r * a ^ r + 21 / 100 * M * (516 : ℝ) ^ r * b ^ r * (E + 1)) ≤
      324 / 100 * (448 * (448 : ℝ) ^ r) *
      (76 / 100 * M ^ r * (1032 : ℝ) ^ r * a ^ r + 21 / 100 * M * (516 : ℝ) ^ r * b ^ r * (E + 1)) := by
    apply mul_le_mul_of_nonneg_right _ hC1
    exact mul_le_mul hL hP1 hP1n (by norm_num)
  have step2 : L * (46 * (r + 1) / (r / 2 - 1)) ^ (r + 1) * (52 / 10 * (35 * M) ^ r * c ^ r) ≤
      324 / 100 * (644 * (644 : ℝ) ^ r) * (52 / 10 * (35 * M) ^ r * c ^ r) := by
    apply mul_le_mul_of_nonneg_right _ hC2
    exact mul_le_mul hL hP2 hP2n (by norm_num)
  have hEE : E + 1 ≤ 2 * E := by linarith
  have hZ : 0 ≤ M * ((448 : ℝ) ^ r * (516 : ℝ) ^ r * b ^ r) := by positivity
  have step3 : 324 / 100 * (448 * (448 : ℝ) ^ r) *
      (76 / 100 * M ^ r * (1032 : ℝ) ^ r * a ^ r + 21 / 100 * M * (516 : ℝ) ^ r * b ^ r * (E + 1)) +
      324 / 100 * (644 * (644 : ℝ) ^ r) * (52 / 10 * (35 * M) ^ r * c ^ r) ≤
      13 * 10 ^ 3 * (46 * 10 ^ 4 * M * c) ^ r + 13 * 10 ^ 3 * M * (46 * 10 ^ 4 * b) ^ r * E := by
    have e1 : 324 / 100 * (448 * (448 : ℝ) ^ r) *
        (76 / 100 * M ^ r * (1032 : ℝ) ^ r * a ^ r + 21 / 100 * M * (516 : ℝ) ^ r * b ^ r * (E + 1)) =
        324 / 100 * 448 * (76 / 100) * ((448 : ℝ) ^ r * (M ^ r * (1032 : ℝ) ^ r * a ^ r)) +
        324 / 100 * 448 * (21 / 100) * (M * ((448 : ℝ) ^ r * (516 : ℝ) ^ r * b ^ r)) * (E + 1) := by
      ring
    have e2 : 324 / 100 * (644 * (644 : ℝ) ^ r) * (52 / 10 * (35 * M) ^ r * c ^ r) =
        324 / 100 * 644 * (52 / 10) * ((644 : ℝ) ^ r * (35 * M) ^ r * c ^ r) := by ring
    rw [e1, e2]
    have hC' : M * ((448 : ℝ) ^ r * (516 : ℝ) ^ r * b ^ r) * (E + 1) ≤
        M * (46 * 10 ^ 4 * b) ^ r * (2 * E) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hC hM0.le) hEE (by linarith) (by positivity)
    have hMYE : 0 ≤ M * (46 * 10 ^ 4 * b) ^ r * E := by positivity
    have hA' := mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 324 / 100 * 448 * (76 / 100))
    have hB' := mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 324 / 100 * 644 * (52 / 10))
    have hC'' := mul_le_mul_of_nonneg_left hC' (by norm_num : (0 : ℝ) ≤ 324 / 100 * 448 * (21 / 100))
    have e3 : 324 / 100 * 448 * (21 / 100) * (M * ((448 : ℝ) ^ r * (516 : ℝ) ^ r * b ^ r)) * (E + 1)
        = 324 / 100 * 448 * (21 / 100) * (M * ((448 : ℝ) ^ r * (516 : ℝ) ^ r * b ^ r) * (E + 1)) := by
      ring
    have e4 : 324 / 100 * 448 * (21 / 100) * (M * (46 * 10 ^ 4 * b) ^ r * (2 * E)) =
        2 * (324 / 100 * 448 * (21 / 100)) * (M * (46 * 10 ^ 4 * b) ^ r * E) := by ring
    rw [e3]
    rw [e4] at hC''
    refine le_trans (add_le_add (add_le_add hA' hC'') hB') ?_
    rw [show 13 * 10 ^ 3 * M * (46 * 10 ^ 4 * b) ^ r * E =
      13 * 10 ^ 3 * (M * (46 * 10 ^ 4 * b) ^ r * E) by ring]
    generalize (46 * 10 ^ 4 * M * c) ^ r = X at hX ⊢
    generalize M * (46 * 10 ^ 4 * b) ^ r * E = Y at hMYE ⊢
    linarith
  linarith


lemma ae_nonneg_of (μ : Measure ℝ) (h0 : μ (Set.Iio 0) = 0) : ∀ᵐ x ∂μ, 0 ≤ x := by
  have hs : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
  rw [ae_iff, hs]; exact h0

/-- Moments of a time law are monotone in the exponent (via `y^r ≤ 1 + y^{r'}` for `y ≥ 0`). -/
lemma moment_fin (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : μ (Set.Iio 0) = 0)
    (r r' : ℝ) (hr : 0 ≤ r) (hrr : r ≤ r') (h : ∫⁻ x, ENNReal.ofReal (x ^ r') ∂μ < ⊤) :
    ∫⁻ x, ENNReal.ofReal (x ^ r) ∂μ < ⊤ := by
  have hle : ∀ᵐ x ∂μ, ENNReal.ofReal (x ^ r) ≤ 1 + ENNReal.ofReal (x ^ r') := by
    filter_upwards [ae_nonneg_of μ h0] with x hx
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (Real.rpow_nonneg hx _)]
    apply ENNReal.ofReal_le_ofReal
    rcases le_total x 1 with h1 | h1
    · have := Real.rpow_le_one hx h1 hr
      have := Real.rpow_nonneg hx r'
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le h1 hrr
      linarith
  calc ∫⁻ x, ENNReal.ofReal (x ^ r) ∂μ ≤ ∫⁻ x, (1 + ENNReal.ofReal (x ^ r')) ∂μ :=
        lintegral_mono_ae hle
    _ = 1 + ∫⁻ x, ENNReal.ofReal (x ^ r') ∂μ := by
        rw [lintegral_add_left measurable_const]; simp
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, h⟩

lemma integrable_rpow (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : μ (Set.Iio 0) = 0)
    (r : ℝ) (h : ∫⁻ x, ENNReal.ofReal (x ^ r) ∂μ < ⊤) : Integrable (fun x : ℝ => x ^ r) μ := by
  refine ⟨(measurable_id.pow_const r).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal ((ae_nonneg_of μ h0).mono (fun x hx => Real.rpow_nonneg hx r))]
  exact h

lemma expo_aux (n μ m x : ℝ) (hn0 : 0 < n) (hμ : 0 < μ) (hd : μ < n) (hm : 0 ≤ m)
    (hx : 0 ≤ x) :
    -((45 : ℝ) / 1000) * ((n - μ) / (n + μ)) * m * x ≤
      -((225 : ℝ) / 10000) * m * ((n - μ) / n * x) := by
  set k := (n - μ) / (n + μ) with hkdef
  have hk : k * (n + μ) = n - μ := div_mul_cancel₀ _ (by linarith)
  have hk0 : 0 ≤ k := div_nonneg (by linarith) (by linarith)
  have hq : (n - μ) / n ≤ 2 * k := by
    rw [div_le_iff₀ hn0]
    nlinarith [mul_nonneg hk0 (by linarith : (0 : ℝ) ≤ n - μ)]
  have hw : 0 ≤ m * x := mul_nonneg hm hx
  have h := mul_le_mul_of_nonneg_right hq hw
  have e1 : -((45 : ℝ) / 1000) * k * m * x = -((45 : ℝ) / 1000) * (k * (m * x)) := by ring
  have e2 : -((225 : ℝ) / 10000) * m * ((n - μ) / n * x) =
      -((225 : ℝ) / 10000) * ((n - μ) / n * (m * x)) := by ring
  rw [e1, e2]
  have e3 : 2 * k * (m * x) = 2 * (k * (m * x)) := by ring
  rw [e3] at h
  generalize k * (m * x) = A at h ⊢
  generalize (n - μ) / n * (m * x) = B at h ⊢
  linarith

end GIGnSBAux

open GIGnSBAux in
theorem solution (n : ℕ) (hn : 1 ≤ n) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (hS1 : mean μS = 1) (hstab : rate μA < n) (hA2 : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μA < ⊤)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : RenewalFamily Ω P n μA μS) (r : ℝ) (hr₁ : (5 : ℝ) / 2 < r) (hr₂ : (r : EReal) < rStar μS)
    (x : ℝ) (hx : 18 ≤ x) :
    P.real {ω | (x : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))} ≤
      13 * 10 ^ 3 * (∫ y, y ^ 2 ∂μS + 1) * ((46 : ℝ) * 10 ^ 4) ^ r *
          ((∫ y, y ^ 2 ∂μS + 1) ^ (r - 1) * r ^ ((5 : ℝ) / 2 * r) +
            r ^ ((3 : ℝ) / 2 * r) * ∫ y, y ^ r ∂μS) *
          ((1 - rho n μA μS) * x) ^ (-(r / 2)) +
        11 / 10 * Real.exp (-((225 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * ((1 - rho n μA μS) * x)) := by
  have hr0 : 0 < r := by linarith
  have hx0 : 0 < x := by linarith
  set μ := rate μA with hμdef
  have hμ : 0 < μ := inv_pos.mpr hA.mean_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hrateS : rate μS = 1 := by rw [rate, hS1]; norm_num
  have hrho : 1 - rho n μA μS = (n - μ) / n := by
    rw [rho, hrateS, mul_one, ← hμdef]; field_simp
  -- finiteness of `E[S^r]` and `E[S^2]`
  obtain ⟨b, hbmem, hrb⟩ := lt_sSup_iff.mp hr₂
  obtain ⟨r', ⟨hr'0, hr'fin⟩, rfl⟩ := hbmem
  have hrr' : r ≤ r' := (EReal.coe_lt_coe_iff.mp hrb).le
  have hSr : ∫⁻ x, ENNReal.ofReal (x ^ r) ∂μS < ⊤ :=
    moment_fin μS hS.nonneg r r' hr0.le hrr' hr'fin
  have hS2r : ∫⁻ x, ENNReal.ofReal (x ^ (2 : ℝ)) ∂μS < ⊤ :=
    moment_fin μS hS.nonneg 2 r (by norm_num) (by linarith) hSr
  have hS2 : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μS < ⊤ := by
    simpa [Real.rpow_two] using hS2r
  -- `M = E[S²] + 1 ≥ 2` and `E = E[S^r] ≥ 1`
  have hI1 : Integrable (fun z : ℝ => z) μS := hS.integrable
  have hI2 : Integrable (fun z : ℝ => z ^ 2) μS := by
    have := integrable_rpow μS hS.nonneg 2 hS2r
    simpa [Real.rpow_two] using this
  have hIr : Integrable (fun z : ℝ => z ^ r) μS := integrable_rpow μS hS.nonneg r hSr
  have hmeanS : ∫ z, z ∂μS = 1 := hS1
  have hM2 : 1 ≤ ∫ y, y ^ 2 ∂μS := by
    have h1 : ∫ z, z ∂μS ≤ ∫ z, (1 + z ^ 2) / 2 ∂μS := by
      have i3 : Integrable (fun z : ℝ => (1 + z ^ 2) / 2) μS :=
        ((integrable_const 1).add hI2).div_const 2
      apply integral_mono hI1 i3
      intro z; show z ≤ (1 + z ^ 2) / 2; nlinarith [sq_nonneg (z - 1)]
    have e3 : ∫ z, (1 + z ^ 2) ∂μS = ∫ z, (1 : ℝ) ∂μS + ∫ z, z ^ 2 ∂μS :=
      integral_add (integrable_const 1) hI2
    rw [integral_div, e3, hmeanS] at h1
    simp at h1
    linarith
  have hEr : 1 ≤ ∫ y, y ^ r ∂μS := by
    have i1 : Integrable (fun z : ℝ => r * (z - 1)) μS := (hI1.sub (integrable_const 1)).const_mul r
    have i2 : Integrable (fun z : ℝ => 1 + r * (z - 1)) μS := (integrable_const 1).add i1
    have h1 : ∫ z, (1 + r * (z - 1)) ∂μS ≤ ∫ z, z ^ r ∂μS := by
      apply integral_mono_ae i2 hIr
      filter_upwards [ae_nonneg_of μS hS.nonneg] with z hz
      have := one_add_mul_self_le_rpow_one_add (s := z - 1) (by linarith) (p := r) (by linarith)
      simpa using this
    have e : ∫ z, (1 + r * (z - 1)) ∂μS = 1 := by
      have ea : ∫ z, (1 + r * (z - 1)) ∂μS = ∫ z, (1 : ℝ) ∂μS + ∫ z, r * (z - 1) ∂μS :=
        integral_add (integrable_const 1) i1
      have eb : ∫ z, (z - 1) ∂μS = ∫ z, z ∂μS - ∫ z, (1 : ℝ) ∂μS :=
        integral_sub hI1 (integrable_const 1)
      rw [ea, integral_const_mul, eb, hmeanS]
      simp
    linarith
  -- apply Theorem 10 with `r₁ = r₂ = r`, `s = r/2`, and the constants of Lemmas 5–6
  set M := ∫ y, y ^ 2 ∂μS + 1 with hM
  set E := ∫ y, y ^ r ∂μS with hE
  set C₁ := 76 / 100 * M ^ r * (1032 : ℝ) ^ r * r ^ (2 * r) +
    21 / 100 * M * (516 : ℝ) ^ r * r ^ ((3 : ℝ) / 2 * r) * (E + 1) with hC₁
  set C₂ := 52 / 10 * (35 * (1 + ∫ y, y ^ 2 ∂μS)) ^ r * r ^ ((5 : ℝ) / 2 * r) with hC₂
  have hM0 : 0 < M := by linarith
  have hC₁pos : 0 < C₁ := by
    have : 0 < 76 / 100 * M ^ r * (1032 : ℝ) ^ r * r ^ (2 * r) := by positivity
    have : 0 ≤ 21 / 100 * M * (516 : ℝ) ^ r * r ^ ((3 : ℝ) / 2 * r) * (E + 1) := by
      have : 0 ≤ E + 1 := by linarith
      positivity
    linarith
  have hC₂pos : 0 < C₂ := by
    have : 0 < 35 * (1 + ∫ y, y ^ 2 ∂μS) := by linarith
    positivity
  have hii : ∀ t : ℝ, 1 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (|∑ i, (F.Ne i ω t : ℝ) - n * t| ^ r) ∂P ≤
        ENNReal.ofReal (C₁ * (n : ℝ) ^ (r / 2) * t ^ (r / 2)) := by
    intro t ht
    have h5 := GIGnBounds.Tail.lemma_5 μS hS hS1 r (by linarith) hSr n hn Ω P F.toServiceFamily t ht
    rw [mul_assoc, ← Real.mul_rpow hn0.le (by linarith)]
    exact h5
  have hiii : ∀ t : ℝ, 2 / (n : ℝ) ≤ t → t ≤ 1 →
      ∫⁻ ω, ENNReal.ofReal (|∑ i, (F.Ne i ω t : ℝ) - n * t| ^ r) ∂P ≤
        ENNReal.ofReal (C₂ * ((n : ℝ) * t) ^ (r / 2)) := by
    intro t ht1 ht2
    exact GIGnBounds.Tail.lemma_6 μS hS hS1 hS2 n hn r (by linarith) Ω P F.toServiceFamily t ht1 ht2
  have h10 := GIGnBounds.Tail.theorem_10 n hn μA μS hA hS hS1 hA2 Ω P F C₁ C₂ r r (r / 2)
    hC₁pos hC₂pos (by linarith) (by linarith) (by linarith) hstab hii hiii x hx
  refine h10.trans ?_
  -- algebra
  have hexp : -(r - r / 2) = -(r / 2) := by ring
  rw [hexp]
  have hd : 0 < (n : ℝ) - μ := by linarith
  have hN : ((1 - rho n μA μS) * x) ^ (-(r / 2)) =
      (n : ℝ) ^ (r / 2) * ((n : ℝ) - μ) ^ (-(r / 2)) * x ^ (-(r / 2)) := by
    rw [hrho, Real.mul_rpow (by positivity) hx0.le, Real.div_rpow hd.le hn0.le,
      Real.rpow_neg hn0.le]
    field_simp
  rw [hN]
  set N := (n : ℝ) ^ (r / 2) * ((n : ℝ) - μ) ^ (-(r / 2)) * x ^ (-(r / 2)) with hNdef
  have hN0 : 0 ≤ N := by positivity
  have hC₂' : C₂ = 52 / 10 * (35 * M) ^ r * r ^ ((5 : ℝ) / 2 * r) := by
    rw [hC₂, hM, add_comm]
  have halg := alg r M E hr₁ (by linarith) hEr
  rw [← hC₂'] at halg
  have hfirst : 18 / 10 * (1 + 1 / (r - r / 2)) * (32 * (r + 1) / (r / 2 - 1)) ^ (r + 1) * C₁ *
        (n : ℝ) ^ (r / 2) * ((n : ℝ) - μ) ^ (-(r / 2)) * x ^ (-(r / 2)) +
      18 / 10 * (1 + 1 / (r - r / 2)) * (46 * (r + 1) / (r / 2 - 1)) ^ (r + 1) * C₂ *
        (n : ℝ) ^ (r / 2) * ((n : ℝ) - μ) ^ (-(r / 2)) * x ^ (-(r / 2)) ≤
      13 * 10 ^ 3 * M * ((46 : ℝ) * 10 ^ 4) ^ r *
        (M ^ (r - 1) * r ^ ((5 : ℝ) / 2 * r) + r ^ ((3 : ℝ) / 2 * r) * E) * N := by
    have := mul_le_mul_of_nonneg_right halg hN0
    refine le_of_eq_of_le ?_ this
    rw [hNdef]
    ring
  -- the exponential term
  have hm0 : 0 ≤ (nMoment μA 2)⁻¹ := by
    apply inv_nonneg.mpr
    apply integral_nonneg
    intro y
    show (0 : ℝ) ≤ (y * rate μA) ^ (2 : ℝ)
    rw [Real.rpow_two]; positivity
  have hexpo : -((45 : ℝ) / 1000) * (((n : ℝ) - μ) / (n + μ)) * (nMoment μA 2)⁻¹ * x ≤
      -((225 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * ((1 - rho n μA μS) * x) := by
    rw [hrho]
    exact expo_aux n μ _ x hn0 hμ hstab hm0 hx0.le
  have hlast : 11 / 10 * Real.exp (-((45 : ℝ) / 1000) * (((n : ℝ) - μ) / (n + μ)) *
        (nMoment μA 2)⁻¹ * x) ≤
      11 / 10 * Real.exp (-((225 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * ((1 - rho n μA μS) * x)) := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpo) (by norm_num)
  linarith
