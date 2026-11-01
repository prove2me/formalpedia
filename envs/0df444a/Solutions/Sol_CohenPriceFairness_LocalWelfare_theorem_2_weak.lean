-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.theorem_2_weak
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T00:45:19.656567+00:00
-- url     : https://prove2.me/submissions/893b1219-3d63-43f9-a06f-5e51a286faef

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families


open Filter Topology Asymptotics Set

namespace CohenPriceFairness.LocalWelfare.Proofs

theorem c1_deriv_est {f : ℝ → ℝ} {m a : ℝ} (hf : HasDerivAt f m a) {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ > 0, ∀ X, |X| < δ → |f (a + X) - f a - X * m| ≤ κ * |X| := by
  have h := (hasDerivAt_iff_isLittleO_nhds_zero.mp hf).def hκ
  rcases Metric.eventually_nhds_iff.mp h with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, fun X hX => ?_⟩
  have := hball (y := X) (by simpa [Real.dist_eq] using hX)
  simpa [Real.norm_eq_abs, smul_eq_mul] using this

theorem c1_core (f g : ℝ → ℝ) (a c m n u w : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hcont : ∃ η > 0, ContinuousOn f (Icc (a - η) (a + η)))
    (hf : HasDerivAt f m a) (hg : HasDerivAt g n c) (hm : m ≠ 0)
    (hv : m * u + n * w = -(f a + g c)) :
    ∀ τ > 0, ∃ ε > 0, ∀ α ∈ Ioc (0 : ℝ) ε, ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧
      |f x + g y| ≤ (1 - α) * |f a + g c| ∧ |x - a - α * u| ≤ τ * α ∧
      |y - c - α * w| ≤ τ * α := by
  intro τ hτ
  obtain ⟨η, hη, hfc⟩ := hcont
  set L := |u| + |w| + τ + 1 with hL
  have hLpos : 0 < L := by positivity
  have hm' : 0 < |m| := abs_pos.mpr hm
  set κ := |m| * τ / (2 * L) with hκdef
  have hκ : 0 < κ := by positivity
  obtain ⟨δ1, hδ1, e1⟩ := c1_deriv_est hf hκ
  obtain ⟨δ2, hδ2, e2⟩ := c1_deriv_est hg hκ
  refine ⟨min 1 (min (δ1 / (2 * L)) (min (δ2 / (2 * L)) (min (η / L) (min (a / L) (c / L))))),
    by positivity, ?_⟩
  rintro α ⟨hα0, hαε⟩
  simp only [le_min_iff] at hαε
  obtain ⟨hα1, hαd1, hαd2, hαη, hαa, hαc⟩ := hαε
  rw [le_div_iff₀ (by positivity)] at hαd1 hαd2
  rw [le_div_iff₀ hLpos] at hαη hαa hαc
  have hu : |u| ≤ L := by rw [hL]; linarith [abs_nonneg w]
  have hw : |w| ≤ L := by rw [hL]; linarith [abs_nonneg u]
  have hut : |u| + τ ≤ L := by rw [hL]; linarith [abs_nonneg w]
  have hαut := mul_le_mul_of_nonneg_left hut hα0.le
  have hαw := mul_le_mul_of_nonneg_left hw hα0.le
  set s := τ * α with hs
  have hs0 : 0 < s := by positivity
  set Δ := f a + g c with hΔ
  let h : ℝ → ℝ := fun t => f (a + α * u + t) + g (c + α * w) - (1 - α) * Δ
  -- key expansion
  have hY : |α * w| < δ2 := by
    rw [abs_mul, abs_of_pos hα0]
    nlinarith [mul_le_mul_of_nonneg_left hw hα0.le]
  have E2 := e2 (α * w) hY
  have key : ∀ t, |t| ≤ s → |h t - m * t| ≤ κ * α * (|u| + τ + |w|) := by
    intro t ht
    have hX : |α * u + t| < δ1 := by
      calc |α * u + t| ≤ |α * u| + |t| := abs_add_le _ _
        _ ≤ α * L := by
          rw [abs_mul, abs_of_pos hα0]
          nlinarith [mul_le_mul_of_nonneg_left hut hα0.le]
        _ < δ1 := by nlinarith
    have E1 := e1 (α * u + t) hX
    have : h t - m * t = (f (a + (α * u + t)) - f a - (α * u + t) * m)
        + (g (c + α * w) - g c - α * w * n) := by
      simp only [h, ← add_assoc]
      have : α * Δ = - (α * (m * u + n * w)) := by rw [hv]; ring
      linear_combination this
    rw [this]
    have hXb : |α * u + t| ≤ α * |u| + α * τ := by
      calc |α * u + t| ≤ |α * u| + |t| := abs_add_le _ _
        _ ≤ α * |u| + α * τ := by rw [abs_mul, abs_of_pos hα0]; linarith
    have hYb : |α * w| = α * |w| := by rw [abs_mul, abs_of_pos hα0]
    calc _ ≤ |f (a + (α * u + t)) - f a - (α * u + t) * m| + |g (c + α * w) - g c - α * w * n| :=
          abs_add_le _ _
      _ ≤ κ * |α * u + t| + κ * |α * w| := add_le_add E1 E2
      _ ≤ κ * (α * |u| + α * τ) + κ * (α * |w|) := by
          rw [hYb]; gcongr
      _ = κ * α * (|u| + τ + |w|) := by ring
  have hbound : κ * α * (|u| + τ + |w|) < |m| * s := by
    have h1 : κ * (|u| + τ + |w|) < |m| * τ := by
      rw [hκdef]
      have : |u| + τ + |w| < 2 * L := by rw [hL]; linarith [abs_nonneg u, abs_nonneg w]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos hm' hτ]
    rw [hs]; nlinarith
  -- continuity of h on [-s, s]
  have hcont_h : ContinuousOn h (uIcc (-s) s) := by
    rw [uIcc_of_le (by linarith)]
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.add _ continuousOn_const
    apply hfc.comp (by fun_prop)
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hau := neg_abs_le u
    have hau' := le_abs_self u
    have h1 := mul_le_mul_of_nonneg_left hau hα0.le
    have h2 := mul_le_mul_of_nonneg_left hau' hα0.le
    constructor <;> nlinarith
  have hsign : (0 : ℝ) ∈ uIcc (h (-s)) (h s) := by
    have k1 := abs_le.mp (le_trans (key s (by rw [abs_of_pos hs0])) hbound.le)
    have k2 := abs_le.mp (le_trans (key (-s) (by rw [abs_neg, abs_of_pos hs0])) hbound.le)
    rw [mul_neg] at k2
    obtain ⟨k1a, k1b⟩ := k1
    obtain ⟨k2a, k2b⟩ := k2
    rw [mem_uIcc]
    rcases lt_or_gt_of_ne hm with hneg | hpos
    · rw [abs_of_neg hneg] at hbound k1a k1b k2a k2b
      right
      constructor <;> linarith
    · rw [abs_of_pos hpos] at hbound k1a k1b k2a k2b
      left
      constructor <;> linarith
  obtain ⟨t, ht, hht⟩ := intermediate_value_uIcc hcont_h hsign
  rw [uIcc_of_le (by linarith)] at ht
  obtain ⟨ht1, ht2⟩ := ht
  refine ⟨a + α * u + t, c + α * w, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left (neg_abs_le u) hα0.le
    have h3 : α * L ≤ a := hαa
    have h4 : α * (|u| + τ) = α * |u| + τ * α := by ring
    have h5 : α * -|u| = -(α * |u|) := by ring
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (neg_abs_le w) hα0.le
    have h5 : α * -|w| = -(α * |w|) := by ring
    have h6 : α * |w| ≤ α * L := hαw
    linarith
  · have : f (a + α * u + t) + g (c + α * w) = (1 - α) * Δ := by
      simp only [h] at hht; linarith
    rw [this, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - α)]
  · rw [show a + α * u + t - a - α * u = t by ring, abs_le]; constructor <;> linarith
  · rw [show c + α * w - c - α * w = 0 by ring, abs_zero]; positivity

theorem core_feasible_curve
    (M : Fin 2 → ℝ → ℝ) (b mm v : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hMd : ∀ i, HasDerivAt (M i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hv : mm 0 * v 0 - mm 1 * v 1 = -(M 0 (b 0) - M 1 (b 1))) :
    ∀ τ > 0, ∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε, ∃ q : Fin 2 → ℝ,
      (∀ i, 0 ≤ q i) ∧
      |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)| ∧
      ∀ i, |q i - b i - α * v i| ≤ τ * α := by
  intro τ hτ
  obtain ⟨η, hη, hc⟩ := hcont
  rcases hmm with h0 | h1
  · obtain ⟨ε, hε, H⟩ := c1_core (M 0) (fun y => -M 1 y) (b 0) (b 1) (mm 0) (-mm 1) (v 0) (v 1)
      (hb 0) (hb 1) ⟨η, hη, hc 0⟩ (hMd 0) (hMd 1).neg h0 (by linear_combination hv) τ hτ
    refine ⟨ε, hε, fun α hα => ?_⟩
    obtain ⟨x, y, hx, hy, hD, hxv, hyv⟩ := H α hα
    refine ⟨![x, y], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simpa
    · simpa [sub_eq_add_neg] using hD
    · intro i; fin_cases i <;> simpa
  · obtain ⟨ε, hε, H⟩ := c1_core (fun y => -M 1 y) (M 0) (b 1) (b 0) (-mm 1) (mm 0) (v 1) (v 0)
      (hb 1) (hb 0) ⟨η, hη, (hc 1).neg⟩ (hMd 1).neg (hMd 0) (neg_ne_zero.mpr h1)
      (by linear_combination hv) τ hτ
    refine ⟨ε, hε, fun α hα => ?_⟩
    obtain ⟨x, y, hx, hy, hD, hxv, hyv⟩ := H α hα
    refine ⟨![y, x], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simpa
    · have e1 : M 0 y - M 1 x = -M 1 x + M 0 y := by ring
      have e2 : M 0 (b 0) - M 1 (b 1) = -M 1 (b 1) + M 0 (b 0) := by ring
      simpa [e1, e2] using hD
    · intro i; fin_cases i <;> simpa

end CohenPriceFairness.LocalWelfare.Proofs


open MeasureTheory ProbabilityTheory
namespace CohenPriceFairness.LocalWelfare.Proofs
open CohenPriceFairness.LocalWelfare

theorem uniform_demand {b p : ℝ} (hb : 0 < b) (hp : 0 ≤ p) :
    ((uniformLaw b) (Set.Ici p)).toReal = max 0 (1 - p / b) := by
  unfold uniformLaw
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ici, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hb.le]
  rcases le_or_gt p b with hpb | hpb
  · have : Set.Ici p ∩ Set.Icc 0 b = Set.Icc p b := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]; constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, hp.trans h1, h3⟩
    rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    rw [max_eq_right (by rw [sub_nonneg, div_le_one hb]; exact hpb)]
    field_simp
  · have : Set.Ici p ∩ Set.Icc 0 b = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨h1, -, h3⟩; linarith
    rw [this, measure_empty, ENNReal.toReal_zero, mul_zero,
      max_eq_left (by rw [sub_nonpos, one_le_div hb]; exact hpb.le)]

theorem uniform_surplus {b p : ℝ} (hb : 0 < b) (hp : 0 ≤ p) (hpb : p ≤ b) :
    ∫ v, max (v - p) 0 ∂(uniformLaw b) = (b - p) ^ 2 / (2 * b) := by
  unfold uniformLaw
  rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal hb.le,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb.le]
  have h1 : ∫ v in (0:ℝ)..b, max (v - p) 0 = (∫ v in (0:ℝ)..p, max (v - p) 0)
      + ∫ v in p..b, max (v - p) 0 := by
    rw [intervalIntegral.integral_add_adjacent_intervals] <;>
      apply Continuous.intervalIntegrable <;> fun_prop
  have h2 : ∫ v in (0:ℝ)..p, max (v - p) 0 = ∫ v in (0:ℝ)..p, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hp] at hx
    simp only
    exact max_eq_right (by linarith [hx.2])
  have h3 : ∫ v in p..b, max (v - p) 0 = ∫ v in p..b, (v - p) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hpb] at hx
    simp only
    exact max_eq_left (by linarith [hx.1])
  rw [h1, h2, h3, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
    intervalIntegrable_const, integral_id]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

theorem uniform_nonbuyer {b p : ℝ} (hb : 0 < b) (hp : 0 < p) (hpb : p ≤ b) :
    (if (uniformLaw b) (Set.Iio p) = 0 then 0
      else (∫ v in Set.Iio p, v ∂(uniformLaw b)) / ((uniformLaw b) (Set.Iio p)).toReal) = p / 2 := by
  have hset : Set.Iio p ∩ Set.Icc 0 b = Set.Ico 0 p := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]; constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  have hmeas : (uniformLaw b) (Set.Iio p) = (ENNReal.ofReal b)⁻¹ * ENNReal.ofReal p := by
    unfold uniformLaw
    rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Iio, smul_eq_mul, hset,
      Real.volume_Ico, sub_zero]
  have hne : (uniformLaw b) (Set.Iio p) ≠ 0 := by
    rw [hmeas]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
      (by simpa using hp)
  rw [if_neg hne, hmeas, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hb.le,
    ENNReal.toReal_ofReal hp.le]
  have hint : ∫ v in Set.Iio p, v ∂(uniformLaw b) = b⁻¹ * (p ^ 2 / 2) := by
    unfold uniformLaw
    rw [Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hb.le, Measure.restrict_restrict measurableSet_Iio, hset,
      integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hp.le, integral_id]
    simp [smul_eq_mul]
  rw [hint]
  field_simp


end CohenPriceFairness.LocalWelfare.Proofs


open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace CohenPriceFairness.LocalWelfare.Proofs

lemma ec_pdfReal_eq (l x : ℝ) :
    exponentialPDFReal l x = if 0 ≤ x then l * Real.exp (-(l * x)) else 0 := by
  simp [exponentialPDFReal, gammaPDFReal]

lemma ec_pdf_toReal {l : ℝ} (hl : 0 < l) (x : ℝ) :
    (exponentialPDF l x).toReal = exponentialPDFReal l x :=
  ENNReal.toReal_ofReal (exponentialPDFReal_nonneg hl x)

lemma ec_integral {l : ℝ} (hl : 0 < l) (g : ℝ → ℝ) :
    ∫ v, g v ∂(expMeasure l) = ∫ v, exponentialPDFReal l v * g v := by
  change ∫ v, g v ∂(volume.withDensity (exponentialPDF l)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (f := exponentialPDF l)
      (measurable_exponentialPDFReal l).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext v
  rw [smul_eq_mul]
  exact congrArg (· * g v) (ec_pdf_toReal hl v)

lemma ec_setIntegral {l : ℝ} (hl : 0 < l) (g : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ v in s, g v ∂(expMeasure l) = ∫ v in s, exponentialPDFReal l v * g v := by
  change ∫ v in s, g v ∂(volume.withDensity (fun x => exponentialPDF l x)) = _
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul (f := exponentialPDF l)
      (measurable_exponentialPDFReal l).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ hs]
  refine setIntegral_congr_fun hs fun v _ => ?_
  rw [smul_eq_mul]
  exact congrArg (· * g v) (ec_pdf_toReal hl v)

instance ec_noAtoms (l : ℝ) : NullSingletonClass (expMeasure l) :=
  ⟨fun x => withDensity_absolutelyContinuous _ _ (measure_singleton x)⟩

lemma ec_Iic_real {l : ℝ} (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p) :
    (expMeasure l).real (Set.Iic p) = 1 - Real.exp (-(l * p)) := by
  have := isProbabilityMeasure_expMeasure hl
  rw [← cdf_eq_real, cdf_expMeasure_eq hl, if_pos hp]

theorem exp_demand {l p : ℝ} (hl : 0 < l) (hp : 0 ≤ p) :
    ((expMeasure l) (Set.Ici p)).toReal = Real.exp (-(l * p)) := by
  have := isProbabilityMeasure_expMeasure hl
  have h1 : (expMeasure l) (Set.Ici p) = (expMeasure l) (Set.Ioi p) :=
    (measure_congr Ioi_ae_eq_Ici).symm
  rw [h1, ← Set.compl_Iic]
  change (expMeasure l).real (Set.Iic p)ᶜ = _
  rw [probReal_compl_eq_one_sub measurableSet_Iic, ec_Iic_real hl hp]
  ring

theorem exp_surplus {l p : ℝ} (hl : 0 < l) (hp : 0 ≤ p) :
    ∫ v, max (v - p) 0 ∂(expMeasure l) = Real.exp (-(l * p)) / l := by
  rw [ec_integral hl]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi p) (fun x hx => by
    simp only [Set.mem_Ioi, not_lt] at hx
    rw [max_eq_right (by linarith), mul_zero])]
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun x => (x - p) * l * Real.exp (-(l * x)))
    (fun x hx => by
      simp only [Set.mem_Ioi] at hx
      rw [ec_pdfReal_eq, if_pos (by linarith), max_eq_left (by linarith)]
      ring)]
  have key := integral_Ioi_of_hasDerivAt_of_nonneg' (a := p) (l := 0)
    (g := fun x => -(x - p + 1 / l) * Real.exp (-(l * x)))
    (g' := fun x => (x - p) * l * Real.exp (-(l * x)))
    (fun x _ => by
      have h : HasDerivAt (fun y => (-1 * (y - p + 1 / l)) * Real.exp (-l * y))
          (-1 * 1 * Real.exp (-l * x) + -1 * (x - p + 1 / l) * (Real.exp (-l * x) * (-l * 1))) x :=
        ((((hasDerivAt_id' x).sub_const p).add_const (1 / l)).const_mul (-1)).mul
          (((hasDerivAt_id' x).const_mul (-l)).exp)
      have e : (fun x => -(x - p + 1 / l) * Real.exp (-(l * x))) =
          (fun y => (-1 * (y - p + 1 / l)) * Real.exp (-l * y)) := by
        funext y; rw [neg_mul l y]; ring
      rw [e]
      refine h.congr_deriv ?_
      rw [neg_mul l x]
      field_simp
      ring)
    (fun x hx => by
      simp only [Set.mem_Ioi] at hx
      have := Real.exp_pos (-(l * x))
      have : 0 ≤ x - p := by linarith
      positivity)
    (by
      have h1 : Tendsto (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-l * x)) atTop (𝓝 0) :=
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 l hl
      have h2 : Tendsto (fun x : ℝ => Real.exp (-(l * x))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hl)
      have h3 := (h1.neg).add (h2.const_mul (p - 1 / l))
      simp only [neg_zero, mul_zero, add_zero] at h3
      refine h3.congr fun x => ?_
      simp only [Real.rpow_one, neg_mul]
      ring)
  rw [key]
  field_simp
  ring

theorem exp_nonbuyer {l p : ℝ} (hl : 0 < l) (hp : 0 < p) :
    (if (expMeasure l) (Set.Iio p) = 0 then 0
      else (∫ v in Set.Iio p, v ∂(expMeasure l)) / ((expMeasure l) (Set.Iio p)).toReal) =
      1 / l - p / (Real.exp (l * p) - 1) := by
  have := isProbabilityMeasure_expMeasure hl
  have hIio : ((expMeasure l) (Set.Iio p)).toReal = 1 - Real.exp (-(l * p)) := by
    rw [measure_congr Iio_ae_eq_Iic]
    exact ec_Iic_real hl hp.le
  have hE : Real.exp (-(l * p)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hne : (expMeasure l) (Set.Iio p) ≠ 0 := by
    intro h
    rw [h] at hIio
    simp at hIio
    linarith
  rw [if_neg hne, hIio, ec_setIntegral hl _ _ measurableSet_Iio]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iio
    (s := Set.Ioo 0 p) Set.Ioo_subset_Iio_self
    (fun x hx => by
      simp only [Set.mem_sdiff, Set.mem_Iio, Set.mem_Ioo, not_and] at hx
      by_cases h0 : 0 ≤ x
      · have : x = 0 := by
          by_contra hx0
          have := hx.2 (lt_of_le_of_ne h0 (Ne.symm hx0))
          linarith [hx.1]
        rw [this, mul_zero]
      · rw [ec_pdfReal_eq, if_neg h0, zero_mul])]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hp.le]
  rw [intervalIntegral.integral_congr (g := fun x => x * l * Real.exp (-(l * x))) (fun x hx => by
    rw [Set.uIcc_of_le hp.le] at hx
    simp only
    rw [ec_pdfReal_eq, if_pos hx.1]
    ring)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => -(x + 1 / l) * Real.exp (-(l * x)))
    (fun x _ => by
      have h : HasDerivAt (fun y => (-1 * (y + 1 / l)) * Real.exp (-l * y))
          (-1 * 1 * Real.exp (-l * x) + -1 * (x + 1 / l) * (Real.exp (-l * x) * (-l * 1))) x :=
        ((((hasDerivAt_id' x).add_const (1 / l))).const_mul (-1)).mul
          (((hasDerivAt_id' x).const_mul (-l)).exp)
      have e : (fun x => -(x + 1 / l) * Real.exp (-(l * x))) =
          (fun y => (-1 * (y + 1 / l)) * Real.exp (-l * y)) := by
        funext y; rw [neg_mul l y]; ring
      rw [e]
      refine h.congr_deriv ?_
      rw [neg_mul l x]
      field_simp
      ring)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hEp : 1 < Real.exp (l * p) := Real.one_lt_exp_iff.mpr (by positivity)
  simp only [mul_zero, neg_zero, Real.exp_zero, zero_add, mul_one]
  rw [Real.exp_neg]
  have h1 : Real.exp (l * p) - 1 ≠ 0 := by linarith
  have h2 : 1 - (Real.exp (l * p))⁻¹ ≠ 0 := by
    have : (Real.exp (l * p))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hEp
    linarith
  have h3 : Real.exp (l * p) ≠ 0 := (Real.exp_pos _).ne'
  have key : 1 - (Real.exp (l * p))⁻¹ = (Real.exp (l * p) - 1) / Real.exp (l * p) := by
    field_simp
  rw [key]
  field_simp
  rw [mul_comm p l] at *
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq h1]
  ring

end CohenPriceFairness.LocalWelfare.Proofs



/-!
# C2 — `core_sensitivity` (the perturbation theorem)

Proof outline:
* `c2_lower`: along the first-order direction `v*` (via `core_feasible_curve`) there are feasible
  points with total profit `≥ R0(b0)+R1(b1) + (Σ r_i/2 v*_i^2 - κ) α^2`.
* `c2_exist`: existence of a constrained maximiser by compactness of a small box.
* `c2_core`: localisation, `P α - b = O(α)`, and the Lagrange identity give `(P α - b)/α → v*`,
  whence the welfare difference quotient converges.
-/

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace CohenPriceFairness.LocalWelfare.Proofs

theorem c2_lin (f : ℝ → ℝ) (c x : ℝ) (hf : HasDerivAt f c x) (u : ℝ → ℝ)
    (hu : Tendsto u (𝓝[>] 0) (𝓝 x)) (hO : (fun α => u α - x) =O[𝓝[>] 0] (fun α => α)) :
    (fun α => f (u α) - f x - c * (u α - x)) =o[𝓝[>] 0] (fun α => α) := by
  have h1 := (hf.isLittleO.comp_tendsto hu).trans_isBigO hO
  refine h1.congr_left ?_
  intro α
  simp [Function.comp, smul_eq_mul, mul_comm]

theorem c2_sq_o : (fun α : ℝ => α ^ 2) =o[𝓝[>] 0] (fun α => α) :=
  (isLittleO_pow_id (by norm_num)).mono nhdsWithin_le_nhds

theorem c2_ev_small (C δ : ℝ) (hδ : 0 < δ) : ∀ᶠ α in 𝓝[>] (0:ℝ), C * α ^ 2 < δ := by
  have : Tendsto (fun α : ℝ => C * α ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun α : ℝ => C * α ^ 2) (𝓝 0) (𝓝 (C * 0 ^ 2)) :=
      (continuous_const.mul (continuous_pow 2)).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  exact this.eventually_lt_const hδ

theorem c2_exists_of_ev (p : ℝ → Prop) (h : ∀ᶠ α in 𝓝[>] (0:ℝ), p α) :
    ∃ ε > 0, ∀ α ∈ Set.Ioc (0:ℝ) ε, p α := by
  rcases (mem_nhdsGT_iff_exists_Ioc_subset).1 h with ⟨u, hu, hsub⟩
  exact ⟨u, hu, fun α hα => hsub hα⟩

theorem c2_lower_i (Ri : ℝ → ℝ) (bi ri vi τ α ρ qi : ℝ) (hr : ri < 0) (hτ : 0 < τ) (hα : 0 < α)
    (hρ : ∀ y, |y| < ρ → |Ri (bi + y) - Ri bi - ri / 2 * y ^ 2| ≤ τ * y ^ 2)
    (hq : |qi - bi - α * vi| ≤ τ * α) (hαρ : α * (|vi| + τ) < ρ) :
    Ri bi + (ri / 2 - τ) * (|vi| + τ) ^ 2 * α ^ 2 ≤ Ri qi := by
  set y := qi - bi with hy
  have hyb : |y| ≤ α * (|vi| + τ) := by
    have h1 : |y| ≤ |y - α * vi| + |α * vi| := by
      have := abs_add_le (y - α * vi) (α * vi)
      simpa using this
    rw [abs_mul, abs_of_pos hα] at h1
    nlinarith
  have hy2 : y ^ 2 ≤ (α * (|vi| + τ)) ^ 2 := by
    have := abs_le.mp hyb
    exact sq_le_sq' this.1 this.2
  have h3 := hρ y (lt_of_le_of_lt hyb hαρ)
  have hq' : bi + y = qi := by rw [hy]; ring
  rw [hq'] at h3
  have h4 := (abs_le.mp h3).1
  have h5 : (ri / 2 - τ) * (α * (|vi| + τ)) ^ 2 ≤ (ri / 2 - τ) * y ^ 2 :=
    mul_le_mul_of_nonpos_left hy2 (by linarith)
  nlinarith

theorem c2_rho (R : ℝ → ℝ) (b r : ℝ)
    (hRt : (fun h => R (b + h) - R b - r / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2))
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ ρ > 0, ∀ y, |y| < ρ → |R (b + y) - R b - r / 2 * y ^ 2| ≤ τ * y ^ 2 := by
  have h := hRt.def hτ
  rcases Metric.eventually_nhds_iff.1 h with ⟨ρ, hρ, hh⟩
  refine ⟨ρ, hρ, fun y hy => ?_⟩
  have := hh (y := y) (by simpa [Real.dist_eq] using hy)
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg y)] using this

theorem c2_lower (R M : Fin 2 → ℝ → ℝ) (b r mm v : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hcontM : ∃ η > 0, ∀ i, ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => R i (b i + h) - R i (b i) - r i / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (M i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hv : mm 0 * v 0 - mm 1 * v 1 = -(M 0 (b 0) - M 1 (b 1))) (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ α in 𝓝[>] (0:ℝ), ∃ q : Fin 2 → ℝ,
      ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
      R 0 (b 0) + R 1 (b 1) + (r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 - κ) * α ^ 2 ≤
        R 0 (q 0) + R 1 (q 1) := by
  set g : ℝ → ℝ := fun τ => (r 0 / 2 - τ) * (|v 0| + τ) ^ 2 + (r 1 / 2 - τ) * (|v 1| + τ) ^ 2
    with hg
  have hgc : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := by
    have : Continuous g := by rw [hg]; fun_prop
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hg0 : g 0 = r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 := by
    simp [hg, sq_abs]
  have hev : ∀ᶠ τ in 𝓝[>] (0:ℝ), r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 - κ < g τ ∧ 0 < τ := by
    refine Filter.Eventually.and ?_ self_mem_nhdsWithin
    rw [← hg0]
    exact hgc.eventually_const_lt (by linarith)
  obtain ⟨τ, hτg, hτ⟩ := hev.exists
  obtain ⟨ρ0, hρ0, hρ0'⟩ := c2_rho (R 0) (b 0) (r 0) (hRt 0) τ hτ
  obtain ⟨ρ1, hρ1, hρ1'⟩ := c2_rho (R 1) (b 1) (r 1) (hRt 1) τ hτ
  obtain ⟨ε1, hε1, hcurve⟩ := core_feasible_curve M b mm v hb hcontM hMd hmm hv τ hτ
  have hsm : ∀ (c ρ : ℝ), 0 < ρ → ∀ᶠ α in 𝓝[>] (0:ℝ), α * c < ρ := by
    intro c ρ hρ
    have : Tendsto (fun α : ℝ => α * c) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun α : ℝ => α * c) (𝓝 0) (𝓝 (0 * c)) :=
        (continuous_id.mul continuous_const).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    exact this.eventually_lt_const hρ
  filter_upwards [Ioc_mem_nhdsGT hε1, hsm (|v 0| + τ) ρ0 hρ0, hsm (|v 1| + τ) ρ1 hρ1]
    with α hα h0 h1
  obtain ⟨q, hq0, hq1, hq2⟩ := hcurve α hα
  refine ⟨q, ⟨hq0, hq1⟩, ?_⟩
  have e0 := c2_lower_i (R 0) (b 0) (r 0) (v 0) τ α ρ0 (q 0) (hr 0) hτ hα.1 hρ0' (hq2 0) h0
  have e1 := c2_lower_i (R 1) (b 1) (r 1) (v 1) τ α ρ1 (q 1) (hr 1) hτ hα.1 hρ1' (hq2 1) h1
  have : (r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 - κ) * α ^ 2 ≤ g τ * α ^ 2 :=
    mul_le_mul_of_nonneg_right hτg.le (sq_nonneg α)
  simp only [hg] at this
  nlinarith

theorem c2_each (R : Fin 2 → ℝ → ℝ) (b : Fin 2 → ℝ)
    (hopt : ∀ i, ∀ p, 0 ≤ p → R i p ≤ R i (b i)) (q : Fin 2 → ℝ) (hq : ∀ i, 0 ≤ q i)
    (δ : ℝ) (h : R 0 (b 0) + R 1 (b 1) - δ ≤ R 0 (q 0) + R 1 (q 1)) :
    ∀ i, R i (b i) - δ ≤ R i (q i) := by
  have h0 := hopt 0 (q 0) (hq 0)
  have h1 := hopt 1 (q 1) (hq 1)
  intro i; fin_cases i <;> simp <;> linarith

theorem c2_exist (R M : Fin 2 → ℝ → ℝ) (b : Fin 2 → ℝ) (C : ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → R i p ≤ R i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → R i (b i) - δ ≤ R i p → |p - b i| < ε)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (R i) (Set.Icc (b i - η) (b i + η)) ∧
      ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hq : ∀ᶠ α in 𝓝[>] (0:ℝ), ∃ q : Fin 2 → ℝ,
      ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
      R 0 (b 0) + R 1 (b 1) + C * α ^ 2 ≤ R 0 (q 0) + R 1 (q 1)) :
    ∃ ε > 0, ∀ α ∈ Set.Icc (0 : ℝ) ε, ∃ p : Fin 2 → ℝ,
      ((∀ i, 0 ≤ p i) ∧ |M 0 (p 0) - M 1 (p 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
      ∀ q : Fin 2 → ℝ,
        ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
        R 0 (q 0) + R 1 (q 1) ≤ R 0 (p 0) + R 1 (p 1) := by
  obtain ⟨η, hη, hc⟩ := hcont
  set ε0 := min η (min (b 0) (b 1)) / 2 with hε0d
  have hm1 : min η (min (b 0) (b 1)) ≤ η := min_le_left _ _
  have hm2 : min η (min (b 0) (b 1)) ≤ b 0 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hm3 : min η (min (b 0) (b 1)) ≤ b 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hmpos : 0 < min η (min (b 0) (b 1)) := lt_min hη (lt_min (hb 0) (hb 1))
  have hε0 : 0 < ε0 := by rw [hε0d]; linarith
  have hε0η : ε0 < η := by rw [hε0d]; linarith
  have hε0b : ∀ i, ε0 < b i := by
    intro i; fin_cases i
    · simp; rw [hε0d]; linarith
    · simp; rw [hε0d]; linarith
  obtain ⟨δ0, hδ0, hl⟩ := hloc ε0 hε0
  obtain ⟨ε, hε, hall⟩ := c2_exists_of_ev _ (hq.and (c2_ev_small (-C) δ0 hδ0))
  refine ⟨ε, hε, fun α hα => ?_⟩
  rcases eq_or_lt_of_le hα.1 with h0 | hpos
  · subst h0
    refine ⟨b, ⟨fun i => (hb i).le, by simp⟩, fun q hq => ?_⟩
    have := hopt 0 (q 0) (hq.1 0)
    have := hopt 1 (q 1) (hq.1 1)
    linarith
  obtain ⟨⟨q, hqf, hqT⟩, hsmall⟩ := hall α ⟨hpos, hα.2⟩
  set B : Set (Fin 2 → ℝ) := Set.univ.pi (fun i => Set.Icc (b i - ε0) (b i + ε0)) with hB
  have inbox : ∀ q' : Fin 2 → ℝ, (∀ i, 0 ≤ q' i) →
      R 0 (b 0) + R 1 (b 1) - δ0 ≤ R 0 (q' 0) + R 1 (q' 1) → q' ∈ B := by
    intro q' hq' hT
    have he := c2_each R b hopt q' hq' δ0 hT
    intro i _
    have := abs_lt.mp (hl i (q' i) (hq' i) (he i))
    constructor <;> linarith [this.1, this.2]
  set g : (Fin 2 → ℝ) → ℝ := fun p => |M 0 (p 0) - M 1 (p 1)| with hg
  set K : Set (Fin 2 → ℝ) := B ∩ g ⁻¹' Set.Iic ((1 - α) * |M 0 (b 0) - M 1 (b 1)|) with hK
  have hBc : IsCompact B := isCompact_univ_pi (fun i => isCompact_Icc)
  have hmaps : ∀ i, Set.MapsTo (fun p : Fin 2 → ℝ => p i) B (Set.Icc (b i - η) (b i + η)) := by
    intro i p hp
    have := hp i (Set.mem_univ _)
    constructor <;> linarith [this.1, this.2]
  have hMc : ∀ i, ContinuousOn (fun p : Fin 2 → ℝ => M i (p i)) B := fun i =>
    (hc i).2.comp (continuous_apply i).continuousOn (hmaps i)
  have hRc : ∀ i, ContinuousOn (fun p : Fin 2 → ℝ => R i (p i)) B := fun i =>
    (hc i).1.comp (continuous_apply i).continuousOn (hmaps i)
  have hgc : ContinuousOn g B := ((hMc 0).sub (hMc 1)).abs
  have hKc : IsCompact K :=
    hBc.of_isClosed_subset (hgc.preimage_isClosed_of_isClosed hBc.isClosed isClosed_Iic)
      Set.inter_subset_left
  have hqB : q ∈ B := inbox q hqf.1 (by nlinarith)
  have hqK : q ∈ K := ⟨hqB, hqf.2⟩
  have hTc : ContinuousOn (fun p : Fin 2 → ℝ => R 0 (p 0) + R 1 (p 1)) K :=
    ((hRc 0).add (hRc 1)).mono Set.inter_subset_left
  obtain ⟨p, hpK, hpmax⟩ := hKc.exists_isMaxOn ⟨q, hqK⟩ hTc
  have hpB := hpK.1
  refine ⟨p, ⟨fun i => ?_, hpK.2⟩, fun q' hq' => ?_⟩
  · have := hpB i (Set.mem_univ _)
    linarith [this.1, hε0b i]
  by_cases h : R 0 (b 0) + R 1 (b 1) - δ0 ≤ R 0 (q' 0) + R 1 (q' 1)
  · exact hpmax ⟨inbox q' hq'.1 h, hq'.2⟩
  · have := hpmax hqK
    have h' := lt_of_not_ge h
    change R 0 (q 0) + R 1 (q 1) ≤ R 0 (p 0) + R 1 (p 1) at this
    linarith

theorem c2_core (R M S : Fin 2 → ℝ → ℝ) (w b r mm σ v : Fin 2 → ℝ) (μ : ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → R i p ≤ R i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → R i (b i) - δ ≤ R i p → |p - b i| < ε)
    (hcontM : ∃ η > 0, ∀ i, ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => R i (b i + h) - R i (b i) - r i / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (M i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hSd : ∀ i, HasDerivAt (S i) (σ i) (b i))
    (hv0 : r 0 * v 0 = μ * mm 0) (hv1 : r 1 * v 1 = -(μ * mm 1))
    (hvl : mm 0 * v 0 - mm 1 * v 1 = -(M 0 (b 0) - M 1 (b 1)))
    (hμΔ : 0 ≤ μ * (M 0 (b 0) - M 1 (b 1)))
    (P : ℝ → Fin 2 → ℝ)
    (hP : ∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε,
        ((∀ i, 0 ≤ P α i) ∧
          |M 0 (P α 0) - M 1 (P α 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
        ∀ q : Fin 2 → ℝ,
          ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
          R 0 (q 0) + R 1 (q 1) ≤ R 0 (P α 0) + R 1 (P α 1)) :
    Tendsto (fun α =>
          ((R 0 (P α 0) + R 1 (P α 1) + w 0 * S 0 (P α 0) + w 1 * S 1 (P α 1)) -
            (R 0 (b 0) + R 1 (b 1) + w 0 * S 0 (b 0) + w 1 * S 1 (b 1))) / α)
        (𝓝[>] 0) (𝓝 (w 0 * σ 0 * v 0 + w 1 * σ 1 * v 1)) := by
  obtain ⟨εP, hεP, hPall⟩ := hP
  have hPev : ∀ᶠ α in 𝓝[>] (0:ℝ), (((∀ i, 0 ≤ P α i) ∧
          |M 0 (P α 0) - M 1 (P α 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
        ∀ q : Fin 2 → ℝ,
          ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
          R 0 (q 0) + R 1 (q 1) ≤ R 0 (P α 0) + R 1 (P α 1)) ∧ 0 < α := by
    filter_upwards [Ioc_mem_nhdsGT hεP] with α hα using ⟨hPall α hα, hα.1⟩
  set Qs := r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 with hQs
  set T0 := R 0 (b 0) + R 1 (b 1) with hT0
  have hQs0 : Qs ≤ 0 := by
    have := hr 0; have := hr 1
    rw [hQs]; nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  -- Step A: lower bound
  have hA : ∀ κ > 0, ∀ᶠ α in 𝓝[>] (0:ℝ),
      T0 + (Qs - κ) * α ^ 2 ≤ R 0 (P α 0) + R 1 (P α 1) := by
    intro κ hκ
    filter_upwards [c2_lower R M b r mm v hb hcontM hr hRt hMd hmm hvl κ hκ, hPev]
      with α hq hP
    obtain ⟨q, hqf, hqT⟩ := hq
    exact le_trans hqT (hP.1.2 q hqf)
  -- Step B: localisation
  have hPt : ∀ i, Tendsto (fun α => P α i) (𝓝[>] 0) (𝓝 (b i)) := by
    intro i
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hl⟩ := hloc ε hε
    filter_upwards [hA 1 one_pos, c2_ev_small (-(Qs - 1)) δ hδ, hPev] with α h1 h2 h3
    have he := c2_each R b hopt (P α) h3.1.1.1 δ (by nlinarith)
    rw [Real.dist_eq]
    exact hl i (P α i) (h3.1.1.1 i) (he i)
  have hdt : ∀ i, Tendsto (fun α => P α i - b i) (𝓝[>] 0) (𝓝 0) := by
    intro i
    simpa using (hPt i).sub_const (b i)
  -- Step C: Taylor of R along P
  have hRo : ∀ i, (fun α => R i (P α i) - R i (b i) - r i / 2 * (P α i - b i) ^ 2) =o[𝓝[>] 0]
      (fun α => (P α i - b i) ^ 2) := by
    intro i
    refine ((hRt i).comp_tendsto (hdt i)).congr_left ?_
    intro α
    simp [Function.comp]
  have hRb : ∀ i, ∀ κ > 0, ∀ᶠ α in 𝓝[>] (0:ℝ),
      |R i (P α i) - R i (b i) - r i / 2 * (P α i - b i) ^ 2| ≤ κ * (P α i - b i) ^ 2 := by
    intro i κ hκ
    filter_upwards [(hRo i).def hκ] with α h
    simpa [Real.norm_eq_abs] using h
  -- Step D: d = O(α)
  set C := 4 * (1 - Qs) / (-r 0) + 4 * (1 - Qs) / (-r 1) with hCdef
  have hr0 := hr 0
  have hr1 := hr 1
  have hC0 : 0 ≤ 4 * (1 - Qs) / (-r 0) := div_nonneg (by linarith) (by linarith)
  have hC1 : 0 ≤ 4 * (1 - Qs) / (-r 1) := div_nonneg (by linarith) (by linarith)
  have hC : 0 ≤ C := by rw [hCdef]; linarith
  have hD : ∀ᶠ α in 𝓝[>] (0:ℝ), ∀ i, (P α i - b i) ^ 2 ≤ C * α ^ 2 := by
    filter_upwards [hA 1 one_pos, hRb 0 (-r 0 / 4) (by linarith), hRb 1 (-r 1 / 4) (by linarith)]
      with α h1 h2 h3
    have a2 := (abs_le.mp h2).2
    have a3 := (abs_le.mp h3).2
    have n0 : 0 ≤ (-r 0) * (P α 0 - b 0) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have n1 : 0 ≤ (-r 1) * (P α 1 - b 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have nα : 0 ≤ α ^ 2 := sq_nonneg α
    have k0 : (-r 0) * (P α 0 - b 0) ^ 2 ≤ 4 * (1 - Qs) * α ^ 2 := by linarith
    have k1 : (-r 1) * (P α 1 - b 1) ^ 2 ≤ 4 * (1 - Qs) * α ^ 2 := by linarith
    have l0 : (P α 0 - b 0) ^ 2 ≤ 4 * (1 - Qs) / (-r 0) * α ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith
    have l1 : (P α 1 - b 1) ^ 2 ≤ 4 * (1 - Qs) / (-r 1) * α ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith
    have m0 : 0 ≤ 4 * (1 - Qs) / (-r 0) * α ^ 2 := mul_nonneg hC0 nα
    have m1 : 0 ≤ 4 * (1 - Qs) / (-r 1) * α ^ 2 := mul_nonneg hC1 nα
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; rw [hCdef]; linarith
    · simp only [Fin.mk_one, Fin.isValue]; rw [hCdef]; linarith
  have hO : ∀ i, (fun α => P α i - b i) =O[𝓝[>] 0] (fun α => α) := by
    intro i
    refine IsBigO.of_bound (Real.sqrt C) ?_
    filter_upwards [hD] with α h
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, Real.sq_sqrt hC, sq_abs]
    exact h i
  -- Step E: linearisations
  have hMo : ∀ i, (fun α => M i (P α i) - M i (b i) - mm i * (P α i - b i)) =o[𝓝[>] 0]
      (fun α => α) := fun i => c2_lin (M i) (mm i) (b i) (hMd i) (fun α => P α i) (hPt i) (hO i)
  have hSo : ∀ i, (fun α => S i (P α i) - S i (b i) - σ i * (P α i - b i)) =o[𝓝[>] 0]
      (fun α => α) := fun i => c2_lin (S i) (σ i) (b i) (hSd i) (fun α => P α i) (hPt i) (hO i)
  have hMb : ∀ i, ∀ κ > 0, ∀ᶠ α in 𝓝[>] (0:ℝ),
      |M i (P α i) - M i (b i) - mm i * (P α i - b i)| ≤ κ * α := by
    intro i κ hκ
    filter_upwards [(hMo i).def hκ, hPev] with α h h'
    simpa [Real.norm_eq_abs, abs_of_pos h'.2] using h
  -- Step F: blow-up converges to v
  have hY : ∀ ε > 0, ∀ᶠ α in 𝓝[>] (0:ℝ),
      -r 0 / 2 * (P α 0 - b 0 - α * v 0) ^ 2 + -r 1 / 2 * (P α 1 - b 1 - α * v 1) ^ 2
        ≤ ε * α ^ 2 := by
    intro ε hε
    set L := 1 + 2 * C + 2 * |μ| with hLdef
    have hL : 0 < L := by rw [hLdef]; positivity
    set κ := ε / L with hκdef
    have hκ : 0 < κ := div_pos hε hL
    have hκL : κ * L = ε := div_mul_cancel₀ ε (ne_of_gt hL)
    filter_upwards [hA κ hκ, hRb 0 κ hκ, hRb 1 κ hκ, hD, hMb 0 κ hκ, hMb 1 κ hκ, hPev]
      with α hA' hR0 hR1 hD' hM0 hM1 hP'
    have hα := hP'.2
    have hfeas := hP'.1.1.2
    have r0a := abs_le.mp hR0
    have r1a := abs_le.mp hR1
    have q1 : -r 0 / 2 * (P α 0 - b 0) ^ 2 + -r 1 / 2 * (P α 1 - b 1) ^ 2 ≤
        (κ - Qs) * α ^ 2 + κ * ((P α 0 - b 0) ^ 2 + (P α 1 - b 1) ^ 2) := by
      linarith [r0a.1, r0a.2, r1a.1, r1a.2]
    have q2 : κ * ((P α 0 - b 0) ^ 2 + (P α 1 - b 1) ^ 2) ≤ κ * (2 * C * α ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hκ.le
      linarith [hD' 0, hD' 1]
    have c1 : μ * (M 0 (P α 0) - M 1 (P α 1)) ≤ (1 - α) * (μ * (M 0 (b 0) - M 1 (b 1))) := by
      calc μ * (M 0 (P α 0) - M 1 (P α 1)) ≤ |μ * (M 0 (P α 0) - M 1 (P α 1))| := le_abs_self _
        _ = |μ| * |M 0 (P α 0) - M 1 (P α 1)| := abs_mul _ _
        _ ≤ |μ| * ((1 - α) * |M 0 (b 0) - M 1 (b 1)|) :=
            mul_le_mul_of_nonneg_left hfeas (abs_nonneg _)
        _ = (1 - α) * |μ * (M 0 (b 0) - M 1 (b 1))| := by rw [abs_mul]; ring
        _ = (1 - α) * (μ * (M 0 (b 0) - M 1 (b 1))) := by rw [abs_of_nonneg hμΔ]
    set e0 := M 0 (P α 0) - M 0 (b 0) - mm 0 * (P α 0 - b 0) with he0
    set e1 := M 1 (P α 1) - M 1 (b 1) - mm 1 * (P α 1 - b 1) with he1
    have c2 : -(μ * (e0 - e1)) ≤ |μ| * (2 * κ * α) := by
      calc -(μ * (e0 - e1)) ≤ |μ * (e0 - e1)| := neg_le_abs _
        _ = |μ| * |e0 - e1| := abs_mul _ _
        _ ≤ |μ| * (|e0| + |e1|) := mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
        _ ≤ |μ| * (2 * κ * α) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have c3 : μ * (mm 0 * (P α 0 - b 0) - mm 1 * (P α 1 - b 1) + α * (M 0 (b 0) - M 1 (b 1)))
        ≤ |μ| * (2 * κ * α) := by
      have eq : μ * (mm 0 * (P α 0 - b 0) - mm 1 * (P α 1 - b 1) + α * (M 0 (b 0) - M 1 (b 1)))
          = μ * (M 0 (P α 0) - M 1 (P α 1)) - (1 - α) * (μ * (M 0 (b 0) - M 1 (b 1)))
            - μ * (e0 - e1) := by rw [he0, he1]; ring
      rw [eq]; linarith
    have c4 := mul_le_mul_of_nonneg_left c3 hα.le
    have iden : -r 0 / 2 * (P α 0 - b 0 - α * v 0) ^ 2 + -r 1 / 2 * (P α 1 - b 1 - α * v 1) ^ 2
        = -r 0 / 2 * (P α 0 - b 0) ^ 2 + -r 1 / 2 * (P α 1 - b 1) ^ 2 + α ^ 2 * Qs
          + α * (μ * (mm 0 * (P α 0 - b 0) - mm 1 * (P α 1 - b 1) + α * (M 0 (b 0) - M 1 (b 1))))
          := by
      rw [hQs]
      linear_combination (α * (P α 0 - b 0) - α ^ 2 * v 0) * hv0
        + (α * (P α 1 - b 1) - α ^ 2 * v 1) * hv1 - α ^ 2 * μ * hvl
    have fin : κ * L * α ^ 2 = ε * α ^ 2 := by rw [hκL]
    rw [iden]
    rw [hLdef] at fin
    linarith [q1, q2, c4, fin]
  have hconv : ∀ i, Tendsto (fun α => (P α i - b i) / α) (𝓝[>] 0) (𝓝 (v i)) := by
    intro i
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hri : 0 < -r i / 2 := by linarith [hr i]
    filter_upwards [hY ((-r i / 2) * (ε ^ 2 / 2)) (by positivity), hPev] with α h hP'
    have hα := hP'.2
    have hi : -r i / 2 * (P α i - b i - α * v i) ^ 2 ≤ (-r i / 2) * (ε ^ 2 / 2) * α ^ 2 := by
      have n0 : 0 ≤ -r 0 / 2 * (P α 0 - b 0 - α * v 0) ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg _)
      have n1 : 0 ≤ -r 1 / 2 * (P α 1 - b 1 - α * v 1) ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg _)
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue] at h ⊢; linarith
      · simp only [Fin.mk_one, Fin.isValue] at h ⊢; linarith
    have hx : (P α i - b i - α * v i) ^ 2 < (ε * α) ^ 2 := by
      have : (P α i - b i - α * v i) ^ 2 ≤ (ε ^ 2 / 2) * α ^ 2 := by
        rw [mul_assoc] at hi
        exact le_of_mul_le_mul_left hi hri
      have hpos : 0 < ε ^ 2 * α ^ 2 := by positivity
      rw [mul_pow]
      linarith
    have hab := abs_lt_of_sq_lt_sq hx (by positivity)
    rw [Real.dist_eq]
    have : (P α i - b i) / α - v i = (P α i - b i - α * v i) / α := by
      field_simp
    rw [this, abs_div, abs_of_pos hα, div_lt_iff₀ hα]
    linarith
  -- Step G: assemble
  have hTo : (fun α => R 0 (P α 0) + R 1 (P α 1) - T0) =o[𝓝[>] 0] (fun α => α) := by
    refine IsBigO.trans_isLittleO ?_ c2_sq_o
    refine IsBigO.of_bound (1 - Qs) ?_
    filter_upwards [hA 1 one_pos, hPev] with α h1 h2
    have u0 := hopt 0 (P α 0) (h2.1.1.1 0)
    have u1 := hopt 1 (P α 1) (h2.1.1.1 1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg α), abs_le]
    constructor <;> nlinarith
  have hS : ∀ i, Tendsto (fun α => (S i (P α i) - S i (b i)) / α) (𝓝[>] 0) (𝓝 (σ i * v i)) := by
    intro i
    have h1 := ((hconv i).const_mul (σ i)).add (hSo i).tendsto_div_nhds_zero
    rw [add_zero] at h1
    refine h1.congr (fun α => ?_)
    ring
  have hall := (hTo.tendsto_div_nhds_zero.add ((hS 0).const_mul (w 0))).add
    ((hS 1).const_mul (w 1))
  have hlim : (0 : ℝ) + w 0 * (σ 0 * v 0) + w 1 * (σ 1 * v 1) = w 0 * σ 0 * v 0 + w 1 * σ 1 * v 1 := by
    ring
  rw [hlim] at hall
  refine hall.congr (fun α => ?_)
  simp only [hT0]
  ring

theorem core_sensitivity
    (R M S : Fin 2 → ℝ → ℝ) (w b r mm σ : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → R i p ≤ R i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → R i (b i) - δ ≤ R i p → |p - b i| < ε)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (R i) (Set.Icc (b i - η) (b i + η)) ∧
      ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => R i (b i + h) - R i (b i) - r i / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (M i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hSd : ∀ i, HasDerivAt (S i) (σ i) (b i))
    (hgap : M 0 (b 0) ≠ M 1 (b 1)) :
    (∃ ε > 0, ∀ α ∈ Set.Icc (0 : ℝ) ε, ∃ p : Fin 2 → ℝ,
      ((∀ i, 0 ≤ p i) ∧ |M 0 (p 0) - M 1 (p 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
      ∀ q : Fin 2 → ℝ,
        ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
        R 0 (q 0) + R 1 (q 1) ≤ R 0 (p 0) + R 1 (p 1)) ∧
    ∀ P : ℝ → Fin 2 → ℝ,
      (∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε,
        ((∀ i, 0 ≤ P α i) ∧
          |M 0 (P α 0) - M 1 (P α 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
        ∀ q : Fin 2 → ℝ,
          ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
          R 0 (q 0) + R 1 (q 1) ≤ R 0 (P α 0) + R 1 (P α 1)) →
      Tendsto (fun α =>
          ((R 0 (P α 0) + R 1 (P α 1) + w 0 * S 0 (P α 0) + w 1 * S 1 (P α 1)) -
            (R 0 (b 0) + R 1 (b 1) + w 0 * S 0 (b 0) + w 1 * S 1 (b 1))) / α)
        (𝓝[>] 0)
        (𝓝 (w 0 * σ 0 * ((-(M 0 (b 0) - M 1 (b 1)) / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
            w 1 * σ 1 * (-((-(M 0 (b 0) - M 1 (b 1)) / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)))) := by
  have hcontM : ∃ η > 0, ∀ i, ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)) := by
    obtain ⟨η, hη, h⟩ := hcont
    exact ⟨η, hη, fun i => (h i).2⟩
  have hr0 := hr 0
  have hr1 := hr 1
  have hK : mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 < 0 := by
    have a0 : mm 0 ^ 2 / r 0 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hr0.le
    have a1 : mm 1 ^ 2 / r 1 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hr1.le
    rcases hmm with h | h
    · have : mm 0 ^ 2 / r 0 < 0 := div_neg_of_pos_of_neg (by positivity) hr0
      linarith
    · have : mm 1 ^ 2 / r 1 < 0 := div_neg_of_pos_of_neg (by positivity) hr1
      linarith
  set Δ := M 0 (b 0) - M 1 (b 1) with hΔ
  set K := mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 with hKdef
  set μ := -Δ / K with hμ
  have hK0 : K ≠ 0 := ne_of_lt hK
  have hr0' : r 0 ≠ 0 := ne_of_lt hr0
  have hr1' : r 1 ≠ 0 := ne_of_lt hr1
  have hμK : μ * K = -Δ := by rw [hμ, div_mul_cancel₀ _ hK0]
  have hμΔ : 0 ≤ μ * Δ := by
    have : μ * Δ = Δ ^ 2 / (-K) := by rw [hμ]; field_simp
    rw [this]; exact div_nonneg (sq_nonneg _) (by linarith)
  set v : Fin 2 → ℝ := ![μ * mm 0 / r 0, -(μ * mm 1 / r 1)] with hvdef
  have hv0 : r 0 * v 0 = μ * mm 0 := by
    show r 0 * (μ * mm 0 / r 0) = μ * mm 0
    field_simp
  have hv1 : r 1 * v 1 = -(μ * mm 1) := by
    show r 1 * -(μ * mm 1 / r 1) = -(μ * mm 1)
    field_simp
  have hvl : mm 0 * v 0 - mm 1 * v 1 = -Δ := by
    rw [← hμK]
    show mm 0 * (μ * mm 0 / r 0) - mm 1 * -(μ * mm 1 / r 1) = μ * K
    rw [hKdef]
    ring
  refine ⟨c2_exist R M b _ hb hopt hloc hcont
    (c2_lower R M b r mm v hb hcontM hr hRt hMd hmm hvl 1 one_pos), fun P hP => ?_⟩
  have := c2_core R M S w b r mm σ v μ hb hopt hloc hcontM hr hRt hMd hmm hSd hv0 hv1 hvl hμΔ P hP
  exact this

end CohenPriceFairness.LocalWelfare.Proofs



open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace CohenPriceFairness.LocalWelfare.Proofs

/-- Generic: `SensitivityClaim` from `core_sensitivity`. -/
theorem ub_claim (m : Market) (b : Prices) (k : Metric) (C : ℝ → Prop) (r mm σ : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → profit m i p ≤ profit m i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p →
      |p - b i| < ε)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η)) ∧
      ContinuousOn (metricValue m k i) (Set.Icc (b i - η) (b i + η)))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => profit m i (b i + h) - profit m i (b i) - r i / 2 * h ^ 2)
      =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (metricValue m k i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hSd : ∀ i, HasDerivAt (surplus m i) (σ i) (b i))
    (hgap : metricValue m k 0 (b 0) ≠ metricValue m k 1 (b 1))
    (hC : C (m.population 0 * σ 0 * ((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
        (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      m.population 1 * σ 1 * (-((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
        (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)))) :
    SensitivityClaim m b k C := by
  obtain ⟨h1, h2⟩ := core_sensitivity (profit m) (metricValue m k) (surplus m) m.population
    b r mm σ hb hopt hloc hcont hr hRt hMd hmm hSd hgap
  refine ⟨?_, ?_⟩
  · obtain ⟨ε, hε, H⟩ := h1
    classical
    let P : ℝ → Prices := fun α =>
      if α = 0 then b else if h : α ∈ Set.Icc (0:ℝ) ε then Classical.choose (H α h) else b
    refine ⟨P, by simp [P], min ε 1, lt_min hε one_pos, min_le_right _ _, ?_⟩
    intro α hα
    have hα1 : α ∈ Set.Icc (0:ℝ) 1 := ⟨hα.1, hα.2.trans (min_le_right _ _)⟩
    by_cases h0 : α = 0
    · subst h0
      have hP : P 0 = b := by simp [P]
      rw [hP]
      refine ⟨⟨hα1, fun i => (hb i).le, ?_⟩, ?_⟩
      · simp
      · intro q hq
        exact add_le_add (hopt 0 _ (hq.2.1 0)) (hopt 1 _ (hq.2.1 1))
    · have hαε : α ∈ Set.Icc (0:ℝ) ε := ⟨hα.1, hα.2.trans (min_le_left _ _)⟩
      have hP : P α = Classical.choose (H α hαε) := by simp only [P, if_neg h0, dif_pos hαε]
      obtain ⟨hfeas, hmax⟩ := Classical.choose_spec (H α hαε)
      rw [hP]
      refine ⟨⟨hα1, hfeas.1, hfeas.2⟩, ?_⟩
      intro q hq
      exact hmax q ⟨hq.2.1, hq.2.2⟩
  · rintro P ⟨hP0, ε, hε, hε1, hP⟩
    refine ⟨_, ?_, hC⟩
    have hyp : ∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε,
        ((∀ i, 0 ≤ P α i) ∧
          |metricValue m k 0 (P α 0) - metricValue m k 1 (P α 1)| ≤
            (1 - α) * |metricValue m k 0 (b 0) - metricValue m k 1 (b 1)|) ∧
        ∀ q : Fin 2 → ℝ,
          ((∀ i, 0 ≤ q i) ∧ |metricValue m k 0 (q 0) - metricValue m k 1 (q 1)| ≤
            (1 - α) * |metricValue m k 0 (b 0) - metricValue m k 1 (b 1)|) →
          profit m 0 (q 0) + profit m 1 (q 1) ≤ profit m 0 (P α 0) + profit m 1 (P α 1) := by
      refine ⟨ε, hε, fun α hα => ?_⟩
      have hαI : α ∈ Set.Icc (0:ℝ) ε := Set.Ioc_subset_Icc_self hα
      obtain ⟨⟨_, hnn, hg⟩, hmax⟩ := hP α hαI
      exact ⟨⟨hnn, hg⟩, fun q hq => hmax q ⟨⟨hαI.1, hαI.2.trans hε1⟩, hq.1, hq.2⟩⟩
    have := h2 P hyp
    show Tendsto (fun α => (welfare m (P α) - welfare m (P 0)) / α) _ _
    rw [hP0]
    exact this

theorem ub_formula_eq (w σ r mm K : Fin 2 → ℝ) (G : ℝ) (hr : ∀ i, r i < 0)
    (hS : mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 ≠ 0)
    (hw : ∀ i, w i * σ i = K i * r i / 2) :
    w 0 * σ 0 * ((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      w 1 * σ 1 * (-((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)) =
    -(G * (K 0 * mm 0 - K 1 * mm 1)) / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1) / 2 := by
  rw [hw 0, hw 1]
  have h0 := (hr 0).ne
  have h1 := (hr 1).ne
  generalize mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 = S at hS ⊢
  field_simp
  ring

theorem ub_sigma_neg (r mm : Fin 2 → ℝ) (hr : ∀ i, r i < 0) (h0 : mm 0 ≠ 0) :
    mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 < 0 := by
  have a : mm 0 ^ 2 / r 0 < 0 := div_neg_of_pos_of_neg (sq_pos_of_ne_zero h0) (hr 0)
  have b : mm 1 ^ 2 / r 1 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hr 1).le
  linarith

theorem ub_sign_pos {S G X : ℝ} (hS : S < 0) (h : 0 < G * X) : 0 < -(G * X) / S / 2 :=
  half_pos (div_pos_of_neg_of_neg (neg_neg_of_pos h) hS)

theorem ub_sign_neg {S G X : ℝ} (hS : S < 0) (h : G * X < 0) : -(G * X) / S / 2 < 0 := by
  have := div_neg_of_pos_of_neg (neg_pos.mpr h) hS
  linarith

/-! Uniform closed forms. -/

theorem ub_demand (m : Market) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p) :
    demand m i p = max 0 (1 - p / bb i) := by
  unfold demand; rw [hlaw i]; exact uniform_demand (hbb i) hp

theorem ub_demand_in (m : Market) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p)
    (hpb : p ≤ bb i) : demand m i p = 1 - p / bb i := by
  rw [ub_demand m bb hbb hlaw i hp]
  apply max_eq_right
  rw [sub_nonneg, div_le_one (hbb i)]; exact hpb

theorem ub_profit_ge (m : Market) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (i : Fin 2) {p : ℝ}
    (hpb : bb i ≤ p) : profit m i p = 0 := by
  unfold profit
  rw [ub_demand m bb hbb hlaw i (le_trans (hbb i).le hpb), max_eq_left]
  · ring
  · rw [sub_nonpos, one_le_div (hbb i)]; exact hpb

theorem ub_quad (d c B p : ℝ) (hB : 0 < B) :
    d * (p - c) * (1 - p / B) = d * (B - c) ^ 2 / (4 * B) - d / B * (p - (B + c) / 2) ^ 2 := by
  field_simp; ring

theorem ub_profit_in (m : Market) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p)
    (hpb : p ≤ bb i) : profit m i p = m.population i * (bb i - m.cost) ^ 2 / (4 * bb i) -
      m.population i / bb i * (p - (bb i + m.cost) / 2) ^ 2 := by
  unfold profit; rw [ub_demand_in m bb hbb hlaw i hp hpb, ub_quad _ _ _ _ (hbb i)]

theorem ub_surplus_in (m : Market) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p)
    (hpb : p ≤ bb i) : surplus m i p = (bb i - p) ^ 2 / (2 * bb i) := by
  unfold surplus; rw [hlaw i]; exact uniform_surplus (hbb i) hp hpb

theorem ub_nonbuyer_in (m : Market) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (i : Fin 2) {p : ℝ} (hp : 0 < p)
    (hpb : p ≤ bb i) : nonbuyer m i p = p / 2 := by
  unfold nonbuyer; rw [hlaw i]; exact uniform_nonbuyer (hbb i) hp hpb

theorem ub_local_deriv {f g : ℝ → ℝ} {a x g' : ℝ} (hx : x ∈ Set.Ioo 0 a)
    (heq : ∀ y ∈ Set.Ioo 0 a, f y = g y) (hg : HasDerivAt g g' x) : HasDerivAt f g' x :=
  hg.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) heq)

theorem ub_local_cont {f g : ℝ → ℝ} {a lo hi : ℝ} (hsub : Set.Icc lo hi ⊆ Set.Ioo 0 a)
    (heq : ∀ y ∈ Set.Ioo 0 a, f y = g y) (hg : Continuous g) :
    ContinuousOn f (Set.Icc lo hi) :=
  hg.continuousOn.congr (fun y hy => heq y (hsub hy))

theorem wk_mono (m : Market) (b : Prices) (k : Metric) (C C' : ℝ → Prop)
    (hw : ∀ D, C D → C' D) (h : SensitivityClaim m b k C) : SensitivityClaim m b k C' := by
  refine ⟨h.1, fun P hP => ?_⟩
  obtain ⟨D, hD, hCD⟩ := h.2 P hP
  exact ⟨D, hD, hw D hCD⟩

/-- Zero baseline gap: the baseline is the unique fair optimum, so the welfare derivative is 0. -/
theorem wk_zero_gap (m : Market) (b : Prices) (k : Metric) (C : ℝ → Prop) (hC : C 0)
    (hb : BaselineOptimal m b) (huniq : ∀ b' : Prices, BaselineOptimal m b' → b' = b)
    (hgap : metricValue m k 0 (b 0) = metricValue m k 1 (b 1)) :
    SensitivityClaim m b k C := by
  have hg : gap m k b = 0 := by unfold gap; rw [hgap, sub_self, abs_zero]
  have hbopt : ∀ α ∈ Set.Icc (0:ℝ) 1, FairOptimal m b k α b := by
    intro α hα
    refine ⟨⟨hα, fun i => (hb i).1, by rw [hg, mul_zero]⟩, fun q hq => ?_⟩
    unfold totalProfit
    exact add_le_add ((hb 0).2 _ (hq.2.1 0)) ((hb 1).2 _ (hq.2.1 1))
  refine ⟨⟨fun _ => b, rfl, 1, one_pos, le_rfl, hbopt⟩, ?_⟩
  rintro P ⟨hP0, ε, hε, hε1, hP⟩
  have hPb : ∀ α ∈ Set.Icc (0:ℝ) ε, P α = b := by
    intro α hα
    have hα1 : α ∈ Set.Icc (0:ℝ) 1 := ⟨hα.1, hα.2.trans hε1⟩
    obtain ⟨⟨_, hnn, _⟩, hmax⟩ := hP α hα
    have hge := hmax b (hbopt α hα1).1
    unfold totalProfit at hge
    have h0 := (hb 0).2 _ (hnn 0)
    have h1 := (hb 1).2 _ (hnn 1)
    have key : ∀ i, profit m i (b i) ≤ profit m i (P α i) := by
      rw [Fin.forall_fin_two]; constructor <;> linarith
    exact huniq _ (fun i => ⟨hnn i, fun p hp => ((hb i).2 p hp).trans (key i)⟩)
  refine ⟨0, ?_, hC⟩
  unfold RightDerivative
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT hε] with α hα
  rw [hPb α ⟨hα.1.le, hα.2.le⟩, hP0, sub_self, zero_div]

theorem goal_uniform (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i) (hne : bb 0 ≠ bb 1)
    (hcb : m.cost < min (bb 0) (bb 1)) (hlaw : ∀ i, m.law i = uniformLaw (bb i)) :
    (∃ b : Prices, BaselineOptimal m b) ∧
    ∀ b : Prices, BaselineOptimal m b →
      SensitivityClaim m b .price (fun D => 0 < D) ∧
      SensitivityClaim m b .nonbuyer (fun D => 0 < D) ∧
      SensitivityClaim m b .demand (fun D => D ≤ 0) ∧
      SensitivityClaim m b .surplus (fun D => D < 0) := by
  have hc0 : m.cost < bb 0 := lt_of_lt_of_le hcb (min_le_left _ _)
  have hc1 : m.cost < bb 1 := lt_of_lt_of_le hcb (min_le_right _ _)
  have hcbi : ∀ i, m.cost < bb i := by rw [Fin.forall_fin_two]; exact ⟨hc0, hc1⟩
  obtain ⟨ps, hps⟩ : ∃ ps : Prices, ps = fun i => (bb i + m.cost) / 2 := ⟨_, rfl⟩
  have hpsi : ∀ i, ps i = (bb i + m.cost) / 2 := fun i => by rw [hps]
  have hps_pos : ∀ i, 0 < ps i := fun i => by rw [hpsi]; linarith [hbb i]
  have hps_lt : ∀ i, ps i < bb i := fun i => by rw [hpsi]; linarith [hcbi i]
  obtain ⟨A, hA⟩ : ∃ A : Fin 2 → ℝ,
      A = fun i => m.population i * (bb i - m.cost) ^ 2 / (4 * bb i) := ⟨_, rfl⟩
  have hApos : ∀ i, 0 < A i := fun i => by
    have := sub_pos.mpr (hcbi i); have := hd i; have := hbb i; rw [hA]; positivity
  have hkpos : ∀ i, 0 < m.population i / bb i := fun i => div_pos (hd i) (hbb i)
  have hRin : ∀ i p, 0 ≤ p → p ≤ bb i →
      profit m i p = A i - m.population i / bb i * (p - ps i) ^ 2 := by
    intro i p hp hpb; rw [ub_profit_in m bb hbb hlaw i hp hpb, hpsi, hA]
  have hRs : ∀ i, profit m i (ps i) = A i := by
    intro i; rw [hRin i _ (hps_pos i).le (hps_lt i).le]; ring
  have hRge : ∀ i p, bb i ≤ p → profit m i p = 0 := fun i p h => ub_profit_ge m bb hbb hlaw i h
  have hopt : ∀ i, ∀ p, 0 ≤ p → profit m i p ≤ profit m i (ps i) := by
    intro i p hp
    rw [hRs]
    rcases le_or_gt p (bb i) with h | h
    · rw [hRin i p hp h]
      have := mul_nonneg (hkpos i).le (sq_nonneg (p - ps i))
      linarith
    · rw [hRge i p h.le]; exact (hApos i).le
  have hBOps : BaselineOptimal m ps := fun i => ⟨(hps_pos i).le, hopt i⟩
  have huniq : ∀ b : Prices, BaselineOptimal m b → b = ps := by
    intro b hb
    funext i
    obtain ⟨hb0, hbm⟩ := hb i
    have h := hbm (ps i) (hps_pos i).le
    rw [hRs] at h
    rcases le_or_gt (b i) (bb i) with h' | h'
    · rw [hRin i _ hb0 h'] at h
      have hx : (b i - ps i) ^ 2 ≤ 0 := by
        by_contra hx; push Not at hx; have := mul_pos (hkpos i) hx; linarith
      have := le_antisymm hx (sq_nonneg _)
      exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp this)
    · rw [hRge i _ h'.le] at h; linarith [hApos i]
  refine ⟨⟨ps, hBOps⟩, ?_⟩
  intro b hb
  have hbps := huniq b hb
  subst b
  have hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (ps i) - δ ≤ profit m i p →
      |p - ps i| < ε := by
    intro ε hε
    have key : ∀ i, ∃ δ > 0, ∀ p, 0 ≤ p → profit m i (ps i) - δ ≤ profit m i p →
        |p - ps i| < ε := by
      intro i
      have hk := hkpos i
      refine ⟨min (A i / 2) (m.population i / bb i * ε ^ 2 / 2),
        lt_min (by linarith [hApos i]) (by positivity), ?_⟩
      intro p hp hle
      have hm1 := min_le_left (A i / 2) (m.population i / bb i * ε ^ 2 / 2)
      have hm2 := min_le_right (A i / 2) (m.population i / bb i * ε ^ 2 / 2)
      rw [hRs] at hle
      rcases le_or_gt p (bb i) with h | h
      · rw [hRin i p hp h] at hle
        apply abs_lt_of_sq_lt_sq _ hε.le
        by_contra hx; push Not at hx
        have := mul_le_mul_of_nonneg_left hx hk.le
        have := mul_pos hk (pow_pos hε 2)
        linarith
      · rw [hRge i p h.le] at hle; linarith [hApos i]
    obtain ⟨δ0, hδ0, H0⟩ := key 0
    obtain ⟨δ1, hδ1, H1⟩ := key 1
    refine ⟨min δ0 δ1, lt_min hδ0 hδ1, ?_⟩
    rw [Fin.forall_fin_two]
    exact ⟨fun p hp hle => H0 p hp (by linarith [min_le_left δ0 δ1]),
      fun p hp hle => H1 p hp (by linarith [min_le_right δ0 δ1])⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min (bb 0 - m.cost) (bb 1 - m.cost) / 4 := ⟨_, rfl⟩
  have hηpos : 0 < η := by
    rw [hη]; have := lt_min (sub_pos.mpr hc0) (sub_pos.mpr hc1); positivity
  have hηle : ∀ i, η ≤ (bb i - m.cost) / 4 := by
    rw [Fin.forall_fin_two, hη]
    exact ⟨by linarith [min_le_left (bb 0 - m.cost) (bb 1 - m.cost)],
      by linarith [min_le_right (bb 0 - m.cost) (bb 1 - m.cost)]⟩
  have hsub : ∀ i, Set.Icc (ps i - η) (ps i + η) ⊆ Set.Ioo 0 (bb i) := by
    intro i x hx
    have := hηle i; have := hpsi i; have := hbb i; have := hcbi i
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmem : ∀ i, ps i ∈ Set.Ioo 0 (bb i) := fun i => ⟨hps_pos i, hps_lt i⟩
  have hRloc : ∀ i, ∀ y ∈ Set.Ioo 0 (bb i),
      profit m i y = A i - m.population i / bb i * (y - ps i) ^ 2 :=
    fun i y hy => hRin i y hy.1.le hy.2.le
  have hcontR : ∀ i, ContinuousOn (profit m i) (Set.Icc (ps i - η) (ps i + η)) :=
    fun i => ub_local_cont (hsub i) (hRloc i) (by fun_prop)
  have hr : ∀ i, -2 * m.population i / bb i < 0 :=
    fun i => div_neg_of_neg_of_pos (by linarith [hd i]) (hbb i)
  have hRt : ∀ i, (fun h => profit m i (ps i + h) - profit m i (ps i) -
      (-2 * m.population i / bb i) / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2) := by
    intro i
    refine (isLittleO_zero (fun h : ℝ => h ^ 2) (𝓝 0)).congr' ?_ EventuallyEq.rfl
    have hmem' : Set.Ioo (-ps i) (bb i - ps i) ∈ 𝓝 (0:ℝ) :=
      Ioo_mem_nhds (by linarith [hps_pos i]) (by linarith [hps_lt i])
    filter_upwards [hmem'] with h hh
    rw [hRloc i _ ⟨by linarith [hh.1], by linarith [hh.2]⟩, hRs]
    ring
  have hSloc : ∀ i, ∀ y ∈ Set.Ioo 0 (bb i), surplus m i y = (bb i - y) ^ 2 / (2 * bb i) :=
    fun i y hy => ub_surplus_in m bb hbb hlaw i hy.1.le hy.2.le
  have hSd : ∀ i, HasDerivAt (surplus m i) (-(bb i - ps i) / bb i) (ps i) := by
    intro i
    apply ub_local_deriv (hmem i) (hSloc i)
    have h1 : HasDerivAt (fun y => bb i - y) (-1) (ps i) :=
      (hasDerivAt_id' (ps i)).const_sub (bb i)
    refine ((h1.fun_pow 2).div_const (2 * bb i)).congr_deriv ?_
    have := (hbb i).ne'
    field_simp
    norm_num
    ring
  have main : ∀ (k : Metric) (C : ℝ → Prop) (mm : Fin 2 → ℝ),
      (∀ i, ContinuousOn (metricValue m k i) (Set.Icc (ps i - η) (ps i + η))) →
      (∀ i, HasDerivAt (metricValue m k i) (mm i) (ps i)) → mm 0 ≠ 0 →
      metricValue m k 0 (ps 0) ≠ metricValue m k 1 (ps 1) →
      (∀ S : ℝ, S < 0 → C (-((metricValue m k 0 (ps 0) - metricValue m k 1 (ps 1)) *
          ((bb 0 - ps 0) * mm 0 - (bb 1 - ps 1) * mm 1)) / S / 2)) →
      SensitivityClaim m ps k C := by
    intro k C mm hcM hMd hmm0 hgap hC
    refine ub_claim m ps k C (fun i => -2 * m.population i / bb i) mm
      (fun i => -(bb i - ps i) / bb i) hps_pos hopt hloc ⟨η, hηpos, fun i => ⟨hcontR i, hcM i⟩⟩
      hr hRt hMd (Or.inl hmm0) hSd hgap ?_
    rw [ub_formula_eq m.population (fun i => -(bb i - ps i) / bb i)
      (fun i => -2 * m.population i / bb i) mm (fun i => bb i - ps i) _ hr
      (ub_sigma_neg _ mm hr hmm0).ne ?_]
    · exact hC _ (ub_sigma_neg _ mm hr hmm0)
    · intro i; have := (hbb i).ne'; field_simp
  have hp0 := hpsi 0
  have hp1 := hpsi 1
  have hb0 := hbb 0
  have hb1 := hbb 1
  have hne' : bb 0 - bb 1 ≠ 0 := sub_ne_zero.mpr hne
  -- price
  have hprice : SensitivityClaim m ps .price (fun D => 0 < D) := by
    refine main .price _ (fun _ => 1) (fun i => continuous_id.continuousOn)
      (fun i => hasDerivAt_id (ps i)) one_ne_zero ?_ (fun S hS => ub_sign_pos hS ?_)
    · show ps 0 ≠ ps 1
      rw [hp0, hp1]; intro h; apply hne; linarith
    · show 0 < (ps 0 - ps 1) * ((bb 0 - ps 0) * 1 - (bb 1 - ps 1) * 1)
      rw [hp0, hp1]
      have e : ((bb 0 + m.cost) / 2 - (bb 1 + m.cost) / 2) *
          ((bb 0 - (bb 0 + m.cost) / 2) * 1 - (bb 1 - (bb 1 + m.cost) / 2) * 1) =
          (bb 0 - bb 1) ^ 2 / 4 := by ring
      rw [e]; have := sq_pos_of_ne_zero hne'; positivity
  -- nonbuyer
  have hNloc : ∀ i, ∀ y ∈ Set.Ioo 0 (bb i), nonbuyer m i y = y / 2 :=
    fun i y hy => ub_nonbuyer_in m bb hbb hlaw i hy.1 hy.2.le
  have hnb : SensitivityClaim m ps .nonbuyer (fun D => 0 < D) := by
    refine main .nonbuyer _ (fun _ => 1 / 2)
      (fun i => ub_local_cont (hsub i) (hNloc i) (by fun_prop))
      (fun i => ub_local_deriv (hmem i) (hNloc i) ((hasDerivAt_id (ps i)).div_const 2))
      (by norm_num) ?_ (fun S hS => ub_sign_pos hS ?_)
    · show nonbuyer m 0 (ps 0) ≠ nonbuyer m 1 (ps 1)
      rw [hNloc 0 _ (hmem 0), hNloc 1 _ (hmem 1), hp0, hp1]; intro h; apply hne; linarith
    · show 0 < (nonbuyer m 0 (ps 0) - nonbuyer m 1 (ps 1)) *
        ((bb 0 - ps 0) * (1 / 2) - (bb 1 - ps 1) * (1 / 2))
      rw [hNloc 0 _ (hmem 0), hNloc 1 _ (hmem 1), hp0, hp1]
      have e : ((bb 0 + m.cost) / 2 / 2 - (bb 1 + m.cost) / 2 / 2) *
          ((bb 0 - (bb 0 + m.cost) / 2) * (1 / 2) - (bb 1 - (bb 1 + m.cost) / 2) * (1 / 2)) =
          (bb 0 - bb 1) ^ 2 / 16 := by ring
      rw [e]; have := sq_pos_of_ne_zero hne'; positivity
  -- demand
  have hDloc : ∀ i, ∀ y ∈ Set.Ioo 0 (bb i), demand m i y = 1 - y / bb i :=
    fun i y hy => ub_demand_in m bb hbb hlaw i hy.1.le hy.2.le
  have hGd : (1 - ps 0 / bb 0) - (1 - ps 1 / bb 1) =
      m.cost * (bb 0 - bb 1) / (2 * bb 0 * bb 1) := by
    rw [hp0, hp1]; field_simp; ring
  have hdem : SensitivityClaim m ps .demand (fun D => D ≤ 0) := by
    rcases hc.eq_or_lt with hzero | hcpos
    · refine wk_zero_gap m ps .demand _ le_rfl hBOps huniq ?_
      show demand m 0 (ps 0) = demand m 1 (ps 1)
      rw [hDloc 0 _ (hmem 0), hDloc 1 _ (hmem 1)]
      have := hGd; rw [← hzero, zero_mul, zero_div] at this; linarith
    have hGd0 : m.cost * (bb 0 - bb 1) / (2 * bb 0 * bb 1) ≠ 0 :=
      div_ne_zero (mul_ne_zero hcpos.ne' hne') (by positivity)
    have hw : ∀ D : ℝ, D < 0 → D ≤ 0 := fun D h => h.le
    refine wk_mono m ps .demand _ _ hw ?_
    refine main .demand _ (fun i => -(1 / bb i))
      (fun i => ub_local_cont (hsub i) (hDloc i) (by fun_prop))
      (fun i => ub_local_deriv (hmem i) (hDloc i)
        (((hasDerivAt_id (ps i)).div_const (bb i)).const_sub 1))
      (neg_ne_zero.mpr (one_div_ne_zero hb0.ne')) ?_ (fun S hS => ub_sign_neg hS ?_)
    · show demand m 0 (ps 0) ≠ demand m 1 (ps 1)
      rw [hDloc 0 _ (hmem 0), hDloc 1 _ (hmem 1)]
      intro h; apply hGd0; rw [← hGd, h, sub_self]
    · show (demand m 0 (ps 0) - demand m 1 (ps 1)) *
        ((bb 0 - ps 0) * -(1 / bb 0) - (bb 1 - ps 1) * -(1 / bb 1)) < 0
      rw [hDloc 0 _ (hmem 0), hDloc 1 _ (hmem 1)]
      have e : (bb 0 - ps 0) * -(1 / bb 0) - (bb 1 - ps 1) * -(1 / bb 1) =
          -((1 - ps 0 / bb 0) - (1 - ps 1 / bb 1)) := by field_simp; ring
      rw [e, hGd]
      have := sq_pos_of_ne_zero hGd0
      nlinarith
  -- surplus
  have hGs : (bb 0 - ps 0) ^ 2 / (2 * bb 0) - (bb 1 - ps 1) ^ 2 / (2 * bb 1) =
      (bb 0 - bb 1) * (bb 0 * bb 1 - m.cost ^ 2) / (8 * bb 0 * bb 1) := by
    rw [hp0, hp1]; field_simp; ring
  have hcc : m.cost ^ 2 < bb 0 * bb 1 := by
    have := mul_lt_mul'' hc0 hc1 hc hc; nlinarith
  have hGs0 : (bb 0 - bb 1) * (bb 0 * bb 1 - m.cost ^ 2) / (8 * bb 0 * bb 1) ≠ 0 :=
    div_ne_zero (mul_ne_zero hne' (sub_pos.mpr hcc).ne') (by positivity)
  have hsur : SensitivityClaim m ps .surplus (fun D => D < 0) := by
    refine main .surplus _ (fun i => -(bb i - ps i) / bb i)
      (fun i => ub_local_cont (hsub i) (hSloc i) (by fun_prop))
      hSd (div_ne_zero (neg_ne_zero.mpr (sub_pos.mpr (hps_lt 0)).ne') hb0.ne') ?_
      (fun S hS => ub_sign_neg hS ?_)
    · show surplus m 0 (ps 0) ≠ surplus m 1 (ps 1)
      rw [hSloc 0 _ (hmem 0), hSloc 1 _ (hmem 1)]
      intro h; apply hGs0; rw [← hGs, h, sub_self]
    · show (surplus m 0 (ps 0) - surplus m 1 (ps 1)) *
        ((bb 0 - ps 0) * (-(bb 0 - ps 0) / bb 0) - (bb 1 - ps 1) * (-(bb 1 - ps 1) / bb 1)) < 0
      rw [hSloc 0 _ (hmem 0), hSloc 1 _ (hmem 1)]
      have e : (bb 0 - ps 0) * (-(bb 0 - ps 0) / bb 0) - (bb 1 - ps 1) * (-(bb 1 - ps 1) / bb 1) =
          -2 * ((bb 0 - ps 0) ^ 2 / (2 * bb 0) - (bb 1 - ps 1) ^ 2 / (2 * bb 1)) := by
        field_simp; ring
      rw [e, hGs]
      have := sq_pos_of_ne_zero hGs0
      nlinarith
  exact ⟨hprice, hnb, hdem, hsur⟩


end CohenPriceFairness.LocalWelfare.Proofs


open MeasureTheory ProbabilityTheory Filter Topology Asymptotics Real Set

/-!
# Exponential branch of `theorem_2_positive_cost` (`goal_exp`)

Uses the stubbed child lemmas `core_sensitivity`, `exp_demand`, `exp_surplus`, `exp_nonbuyer`.
-/

namespace CohenPriceFairness.LocalWelfare.Proofs

lemma eb_pos_of_deriv (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f 0 = 0)
    (hpos : ∀ x > 0, 0 < f' x) : ∀ x > 0, 0 < f x := by
  have hmono : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x _ => (hf x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hf x).deriv]; exact hpos x hx
  intro x hx
  have := hmono (self_mem_Ici) (le_of_lt hx : (0:ℝ) ≤ x) hx
  rwa [h0] at this

lemma eb_anti_of_deriv (f f' : ℝ → ℝ) (a : ℝ) (hf : ∀ x > a, HasDerivAt f (f' x) x)
    (hneg : ∀ x > a, f' x < 0) : StrictAntiOn f (Ioi a) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi a)
  · exact fun x hx => (hf x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hf x hx).deriv]; exact hneg x hx

lemma eb_A_pos : ∀ x > 0, 0 < x * exp x - exp x + 1 := by
  apply eb_pos_of_deriv (fun x => x * exp x - exp x + 1) (fun x => x * exp x)
  · intro x
    have := (((hasDerivAt_id x).mul (hasDerivAt_exp x)).sub (hasDerivAt_exp x)).add_const 1
    exact this.congr_deriv (by simp)
  · simp
  · intro x hx; positivity

lemma eb_phi_pos : ∀ x > 0, 0 < x * (exp x + 1) - 2 * (exp x - 1) := by
  apply eb_pos_of_deriv _ (fun x => x * exp x - exp x + 1)
  · intro x
    have := ((hasDerivAt_id x).mul ((hasDerivAt_exp x).add_const 1)).sub
      (((hasDerivAt_exp x).sub_const 1).const_mul 2)
    exact this.congr_deriv (by simp; ring)
  · simp
  · exact eb_A_pos

lemma eb_psi1_pos : ∀ x > 0, 0 < exp x - 2 * exp (-x) - 2 * x + 1 := by
  apply eb_pos_of_deriv _ (fun x => exp x + 2 * exp (-x) - 2)
  · intro x
    have h1 := (hasDerivAt_exp x)
    have h2 := (hasDerivAt_neg x).exp
    have := ((h1.sub (h2.const_mul 2)).sub ((hasDerivAt_id x).const_mul 2)).add_const 1
    exact this.congr_deriv (by simp)
  · simp; norm_num
  · intro x hx
    have hts : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
    have h3 : 0 < exp (-x) := exp_pos _
    nlinarith [mul_pos h3 (by positivity : 0 < (exp x - 1)^2 + 1)]

lemma eb_psi_pos : ∀ x > 0, 0 < exp x + 2 * exp (-x) - (x ^ 2 - x + 3) := by
  apply eb_pos_of_deriv _ (fun x => exp x - 2 * exp (-x) - 2 * x + 1)
  · intro x
    have h1 := (hasDerivAt_exp x)
    have h2 := (hasDerivAt_neg x).exp
    have := (h1.add (h2.const_mul 2)).sub ((((hasDerivAt_id x).pow 2).sub (hasDerivAt_id x)).add_const 3)
    exact this.congr_deriv (by simp; ring)
  · simp; norm_num
  · exact eb_psi1_pos

/-! ## Monotonicity facts behind the nonbuyer sign -/

/-- g(x) = (e^x - 1 - x)/((x-1)(e^x-1)) -/
noncomputable def eb_g (x : ℝ) : ℝ := (exp x - 1 - x) / ((x - 1) * (exp x - 1))

/-- h(x) = (x e^x - e^x + 1)/(e^x-1)^2 -/
noncomputable def eb_h (x : ℝ) : ℝ := (x * exp x - exp x + 1) / (exp x - 1) ^ 2

lemma eb_g_anti : StrictAntiOn eb_g (Ioi 1) := by
  apply eb_anti_of_deriv eb_g
    (fun x => ((exp x - 1) * ((x - 1) * (exp x - 1)) - (exp x - 1 - x) * (x * exp x - 1)) /
      ((x - 1) * (exp x - 1)) ^ 2) 1
  · intro x hx
    have hx1 : x - 1 ≠ 0 := by linarith [show (1:ℝ) < x from hx]
    have he : exp x - 1 ≠ 0 := by
      have : 1 < exp x := one_lt_exp_iff.mpr (by linarith [show (1:ℝ) < x from hx])
      linarith
    have := (((hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x)).div
      (((hasDerivAt_id x).sub_const 1).mul ((hasDerivAt_exp x).sub_const 1)) (mul_ne_zero hx1 he)
    exact this.congr_deriv (by simp only [Pi.mul_apply, Pi.sub_apply, id]; ring)
  · intro x hx
    have hx' : (1:ℝ) < x := hx
    have hts : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
    have hψ := eb_psi_pos x (by linarith)
    have hnum : (exp x - 1) * ((x - 1) * (exp x - 1)) - (exp x - 1 - x) * (x * exp x - 1) =
        -(exp x * (exp x + 2 * exp (-x) - (x ^ 2 - x + 3))) := by
      linear_combination 2 * hts
    rw [hnum]
    apply div_neg_of_neg_of_pos
    · have := exp_pos x; nlinarith
    · have : 1 < exp x := one_lt_exp_iff.mpr (by linarith)
      have : 0 < (x - 1) * (exp x - 1) := mul_pos (by linarith) (by linarith)
      positivity

lemma eb_h_pos : ∀ x > 0, 0 < eb_h x := by
  intro x hx
  unfold eb_h
  have : 1 < exp x := one_lt_exp_iff.mpr hx
  have := eb_A_pos x hx
  have : 0 < (exp x - 1) ^ 2 := by nlinarith
  positivity

lemma eb_h_anti : StrictAntiOn eb_h (Ioi 0) := by
  apply eb_anti_of_deriv eb_h
    (fun x => -(exp x * (x * (exp x + 1) - 2 * (exp x - 1))) / (exp x - 1) ^ 3) 0
  · intro x hx
    have he : exp x - 1 ≠ 0 := by
      have : 1 < exp x := one_lt_exp_iff.mpr hx
      linarith
    have := ((((hasDerivAt_id x).mul (hasDerivAt_exp x)).sub (hasDerivAt_exp x)).add_const 1).div
      (((hasDerivAt_exp x).sub_const 1).pow 2) (pow_ne_zero 2 he)
    exact this.congr_deriv (by simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id]; field_simp; ring)
  · intro x hx
    have : 1 < exp x := one_lt_exp_iff.mpr hx
    have hφ := eb_phi_pos x hx
    apply div_neg_of_neg_of_pos
    · have := exp_pos x; nlinarith [mul_pos this hφ]
    · have : 0 < exp x - 1 := by linarith
      positivity

noncomputable def eb_k (x : ℝ) : ℝ := eb_h x / (x - 1)

lemma eb_k_anti : StrictAntiOn eb_k (Ioi 1) := by
  intro a ha b hb hab
  have ha' : (1:ℝ) < a := ha
  have hb' : (1:ℝ) < b := hb
  unfold eb_k
  have h1 : eb_h b < eb_h a := eb_h_anti (show (0:ℝ) < a by linarith) (show (0:ℝ) < b by linarith) hab
  have h2 : 0 < eb_h b := eb_h_pos b (by linarith)
  calc eb_h b / (b - 1) < eb_h b / (a - 1) := by
        apply div_lt_div_of_pos_left h2 (by linarith) (by linarith)
    _ < eb_h a / (a - 1) := by apply div_lt_div_of_pos_right h1 (by linarith)


/-! ## Generic: `SensitivityClaim` from `core_sensitivity` -/

theorem eb_claim (m : Market) (b : Prices) (k : Metric) (C : ℝ → Prop) (r mm σ : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → profit m i p ≤ profit m i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p →
      |p - b i| < ε)
    (hRc : ∀ i, ContinuousOn (profit m i) (Ioi 0))
    (hMc : ∀ i, ContinuousOn (metricValue m k i) (Ioi 0))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => profit m i (b i + h) - profit m i (b i) - r i / 2 * h ^ 2)
      =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (metricValue m k i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hSd : ∀ i, HasDerivAt (surplus m i) (σ i) (b i))
    (hgap : metricValue m k 0 (b 0) ≠ metricValue m k 1 (b 1))
    (hC : C (m.population 0 * σ 0 * ((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
        (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      m.population 1 * σ 1 * (-((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
        (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)))) :
    SensitivityClaim m b k C := by
  have hcont : ∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η)) ∧
      ContinuousOn (metricValue m k i) (Set.Icc (b i - η) (b i + η)) := by
    refine ⟨min (b 0) (b 1) / 2, by have := hb 0; have := hb 1; positivity, fun i => ?_⟩
    have hsub : Set.Icc (b i - min (b 0) (b 1) / 2) (b i + min (b 0) (b 1) / 2) ⊆ Ioi 0 := by
      intro p hp
      have hmin : min (b 0) (b 1) ≤ b i := by
        fin_cases i
        · exact min_le_left _ _
        · exact min_le_right _ _
      have := hb 0; have := hb 1
      have : 0 < min (b 0) (b 1) := lt_min (hb 0) (hb 1)
      simp only [mem_Ioi]; linarith [hp.1]
    exact ⟨(hRc i).mono hsub, (hMc i).mono hsub⟩
  obtain ⟨h1, h2⟩ := core_sensitivity (profit m) (metricValue m k) (surplus m) m.population
    b r mm σ hb hopt hloc hcont hr hRt hMd hmm hSd hgap
  refine ⟨?_, ?_⟩
  · obtain ⟨ε, hε, H⟩ := h1
    classical
    let P : ℝ → Prices := fun α =>
      if α = 0 then b else if h : α ∈ Set.Icc (0:ℝ) ε then Classical.choose (H α h) else b
    refine ⟨P, by simp [P], min ε 1, lt_min hε one_pos, min_le_right _ _, ?_⟩
    intro α hα
    have hα1 : α ∈ Set.Icc (0:ℝ) 1 := ⟨hα.1, hα.2.trans (min_le_right _ _)⟩
    by_cases h0 : α = 0
    · subst h0
      have hP : P 0 = b := by simp [P]
      rw [hP]
      refine ⟨⟨hα1, fun i => (hb i).le, ?_⟩, ?_⟩
      · simp
      · intro q hq
        exact add_le_add (hopt 0 _ (hq.2.1 0)) (hopt 1 _ (hq.2.1 1))
    · have hαε : α ∈ Set.Icc (0:ℝ) ε := ⟨hα.1, hα.2.trans (min_le_left _ _)⟩
      have hP : P α = Classical.choose (H α hαε) := by simp only [P, if_neg h0, dif_pos hαε]
      obtain ⟨hfeas, hmax⟩ := Classical.choose_spec (H α hαε)
      rw [hP]
      refine ⟨⟨hα1, hfeas.1, hfeas.2⟩, ?_⟩
      intro q hq
      exact hmax q ⟨hq.2.1, hq.2.2⟩
  · rintro P ⟨hP0, ε, hε, hε1, hP⟩
    refine ⟨_, ?_, hC⟩
    have hyp : ∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε,
        ((∀ i, 0 ≤ P α i) ∧
          |metricValue m k 0 (P α 0) - metricValue m k 1 (P α 1)| ≤
            (1 - α) * |metricValue m k 0 (b 0) - metricValue m k 1 (b 1)|) ∧
        ∀ q : Fin 2 → ℝ,
          ((∀ i, 0 ≤ q i) ∧ |metricValue m k 0 (q 0) - metricValue m k 1 (q 1)| ≤
            (1 - α) * |metricValue m k 0 (b 0) - metricValue m k 1 (b 1)|) →
          profit m 0 (q 0) + profit m 1 (q 1) ≤ profit m 0 (P α 0) + profit m 1 (P α 1) := by
      refine ⟨ε, hε, fun α hα => ?_⟩
      have hαI : α ∈ Set.Icc (0:ℝ) ε := Set.Ioc_subset_Icc_self hα
      obtain ⟨⟨_, hnn, hg⟩, hmax⟩ := hP α hαI
      exact ⟨⟨hnn, hg⟩, fun q hq => hmax q ⟨⟨hαI.1, hαI.2.trans hε1⟩, hq.1, hq.2⟩⟩
    have := h2 P hyp
    show Tendsto (fun α => (welfare m (P α) - welfare m (P 0)) / α) _ _
    rw [hP0]
    exact this

/-! ## Sign of the formula -/

lemma eb_K_neg (mm r : Fin 2 → ℝ) (hr : ∀ i, r i < 0) (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0) :
    mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 < 0 := by
  have a0 : mm 0 ^ 2 / r 0 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hr 0).le
  have a1 : mm 1 ^ 2 / r 1 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hr 1).le
  rcases hmm with h | h
  · have : mm 0 ^ 2 / r 0 < 0 := div_neg_of_pos_of_neg (by positivity) (hr 0)
    linarith
  · have : mm 1 ^ 2 / r 1 < 0 := div_neg_of_pos_of_neg (by positivity) (hr 1)
    linarith

lemma eb_D_eq (w σ mm r : Fin 2 → ℝ) (G : ℝ) :
    w 0 * σ 0 * ((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      w 1 * σ 1 * (-((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)) =
    (G * (w 0 * σ 0 * mm 0 / r 0 - w 1 * σ 1 * mm 1 / r 1)) *
      (-(mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)⁻¹) := by
  ring

lemma eb_D_pos (w σ mm r : Fin 2 → ℝ) (G : ℝ) (hr : ∀ i, r i < 0) (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (h : 0 < G * (w 0 * σ 0 * mm 0 / r 0 - w 1 * σ 1 * mm 1 / r 1)) :
    0 < w 0 * σ 0 * ((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      w 1 * σ 1 * (-((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)) := by
  rw [eb_D_eq]
  have := eb_K_neg mm r hr hmm
  exact mul_pos h (neg_pos.mpr (inv_lt_zero.mpr this))

lemma eb_D_neg (w σ mm r : Fin 2 → ℝ) (G : ℝ) (hr : ∀ i, r i < 0) (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (h : G * (w 0 * σ 0 * mm 0 / r 0 - w 1 * σ 1 * mm 1 / r 1) < 0) :
    w 0 * σ 0 * ((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      w 1 * σ 1 * (-((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)) < 0 := by
  rw [eb_D_eq]
  have := eb_K_neg mm r hr hmm
  exact mul_neg_of_neg_of_pos h (neg_pos.mpr (inv_lt_zero.mpr this))

/-! ## Closed-form profit -/

noncomputable def eb_R (l d c p : ℝ) : ℝ := d * (p - c) * exp (-(l * p))

lemma eb_R_hasDeriv (l d c p : ℝ) :
    HasDerivAt (eb_R l d c) (d * exp (-(l * p)) * (1 - l * (p - c))) p := by
  have h1 := ((hasDerivAt_id' p).sub_const c).const_mul d
  have h2 := ((hasDerivAt_id' p).const_mul l).neg.exp
  have := h1.mul h2
  exact this.congr_deriv (by simp only [Pi.neg_apply]; ring)

lemma eb_R_strictMono {l d : ℝ} (c : ℝ) (hl : 0 < l) (hd : 0 < d) :
    StrictMonoOn (eb_R l d c) (Iic (c + 1 / l)) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic _)
  · exact fun x _ => (eb_R_hasDeriv l d c x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Iic] at hx
    rw [(eb_R_hasDeriv l d c x).deriv]
    have hx' : x < c + 1 / l := hx
    have : l * (x - c) < 1 := by
      have := mul_lt_mul_of_pos_left (show x - c < 1 / l by linarith) hl
      rwa [mul_one_div_cancel hl.ne'] at this
    have := exp_pos (-(l * x))
    apply mul_pos (mul_pos hd this); linarith

lemma eb_R_strictAnti {l d : ℝ} (c : ℝ) (hl : 0 < l) (hd : 0 < d) :
    StrictAntiOn (eb_R l d c) (Ici (c + 1 / l)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · exact fun x _ => (eb_R_hasDeriv l d c x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(eb_R_hasDeriv l d c x).deriv]
    have hx' : c + 1 / l < x := hx
    have : 1 < l * (x - c) := by
      have := mul_lt_mul_of_pos_left (show 1 / l < x - c by linarith) hl
      rwa [mul_one_div_cancel hl.ne'] at this
    have := exp_pos (-(l * x))
    apply mul_neg_of_pos_of_neg (mul_pos hd this); linarith

lemma eb_R_lt {l d : ℝ} (c : ℝ) (hl : 0 < l) (hd : 0 < d) {p : ℝ} (hp : p ≠ c + 1 / l) :
    eb_R l d c p < eb_R l d c (c + 1 / l) := by
  rcases lt_or_gt_of_ne hp with h | h
  · exact eb_R_strictMono c hl hd (mem_Iic.mpr h.le) (mem_Iic.mpr le_rfl) h
  · exact eb_R_strictAnti c hl hd (mem_Ici.mpr le_rfl) (mem_Ici.mpr h.le) h

lemma eb_R_le {l d : ℝ} (c : ℝ) (hl : 0 < l) (hd : 0 < d) (p : ℝ) :
    eb_R l d c p ≤ eb_R l d c (c + 1 / l) := by
  by_cases hp : p = c + 1 / l
  · rw [hp]
  · exact (eb_R_lt c hl hd hp).le

lemma eb_R_loc {l d : ℝ} (c : ℝ) (hl : 0 < l) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p, eb_R l d c (c + 1 / l) - δ ≤ eb_R l d c p → |p - (c + 1 / l)| < ε := by
  set b := c + 1 / l with hbdef
  have h1 : eb_R l d c (b - ε) < eb_R l d c b := eb_R_lt c hl hd (by linarith)
  have h2 : eb_R l d c (b + ε) < eb_R l d c b := eb_R_lt c hl hd (by linarith)
  refine ⟨min (eb_R l d c b - eb_R l d c (b - ε)) (eb_R l d c b - eb_R l d c (b + ε)) / 2,
    by positivity, fun p hp => ?_⟩
  have m1 := min_le_left (eb_R l d c b - eb_R l d c (b - ε)) (eb_R l d c b - eb_R l d c (b + ε))
  have m2 := min_le_right (eb_R l d c b - eb_R l d c (b - ε)) (eb_R l d c b - eb_R l d c (b + ε))
  rw [abs_lt]
  by_contra hcon
  rcases not_and_or.mp hcon with h | h
  · replace h := not_lt.mp h
    have : eb_R l d c p ≤ eb_R l d c (b - ε) :=
      (eb_R_strictMono c hl hd).monotoneOn (mem_Iic.mpr (by linarith)) (mem_Iic.mpr (by linarith))
        (by linarith)
    linarith
  · replace h := not_lt.mp h
    have : eb_R l d c p ≤ eb_R l d c (b + ε) :=
      (eb_R_strictAnti c hl hd).antitoneOn (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith))
        (by linarith)
    linarith

lemma eb_exp3 {u : ℝ} (hu : |u| ≤ 1) : |exp u - (1 + u + u ^ 2 / 2)| ≤ |u| ^ 3 := by
  have hE := Real.exp_bound hu (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, u ^ m / (m.factorial : ℝ) = 1 + u + u ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at hE
  refine hE.trans (mul_le_of_le_one_right (by positivity) ?_)
  norm_num [Nat.factorial]

lemma eb_R_taylor {l : ℝ} (d c : ℝ) (hl : 0 < l) :
    (fun h => eb_R l d c (c + 1 / l + h) - eb_R l d c (c + 1 / l) -
      (-(d * l * exp (-(l * (c + 1 / l))))) / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2) := by
  apply IsBigO.trans_isLittleO _ (isLittleO_pow_pow (show 2 < 3 by norm_num))
  apply IsBigO.of_bound (5 / 2 * |d| * exp (-(l * (c + 1 / l))) * l ^ 2)
  have hl1 : 0 < 1 / l := one_div_pos.mpr hl
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hl1) hl1] with h hh
  have hu : |-(l * h)| ≤ 1 := by
    rw [abs_neg, abs_le]
    have a := mul_lt_mul_of_pos_left hh.2 hl
    have b := mul_lt_mul_of_pos_left hh.1 hl
    rw [mul_one_div_cancel hl.ne'] at a
    rw [mul_neg, mul_one_div_cancel hl.ne'] at b
    constructor <;> linarith
  have hE := eb_exp3 hu
  set u := -(l * h) with hu_def
  set q := exp (-(l * (c + 1 / l))) with hq
  set E := exp u - (1 + u + u ^ 2 / 2) with hE_def
  have hE2 : |E| ≤ |u| ^ 3 := hE
  have key : eb_R l d c (c + 1 / l + h) - eb_R l d c (c + 1 / l) -
      (-(d * l * q)) / 2 * h ^ 2 = d * q / l * (-u ^ 3 / 2 + (1 - u) * E) := by
    unfold eb_R
    have : exp (-(l * (c + 1 / l + h))) = q * exp u := by
      rw [hq, hu_def, ← exp_add]; ring_nf
    rw [this, ← hq, hE_def, hu_def]
    field_simp
    ring
  rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  have hq0 : 0 < q := exp_pos _
  have habs1 : |d * q / l| = |d| * q / l := by
    rw [abs_div, abs_mul, abs_of_pos hq0, abs_of_pos hl]
  have hu1 : |u| ≤ 1 := hu
  have h1u : |1 - u| ≤ 2 := by
    have := abs_sub (1:ℝ) u; rw [abs_one] at this; linarith
  have hY : |-u ^ 3 / 2 + (1 - u) * E| ≤ 5 / 2 * |u| ^ 3 := by
    have a1 : |-u ^ 3 / 2| = |u| ^ 3 / 2 := by
      rw [neg_div, abs_neg, abs_div, abs_pow]; norm_num
    have a2 : |(1 - u) * E| ≤ 2 * |u| ^ 3 := by
      rw [abs_mul]
      exact mul_le_mul h1u hE2 (abs_nonneg _) (by norm_num)
    calc |-u ^ 3 / 2 + (1 - u) * E| ≤ |-u ^ 3 / 2| + |(1 - u) * E| := abs_add_le _ _
      _ ≤ 5 / 2 * |u| ^ 3 := by rw [a1]; linarith
  have hu3 : |u| ^ 3 = l ^ 3 * |h| ^ 3 := by
    rw [hu_def, abs_neg, abs_mul, abs_of_pos hl, mul_pow]
  rw [habs1, abs_pow]
  have hdq : 0 ≤ |d| * q / l := by positivity
  calc |d| * q / l * |-u ^ 3 / 2 + (1 - u) * E| ≤ |d| * q / l * (5 / 2 * |u| ^ 3) :=
        mul_le_mul_of_nonneg_left hY hdq
    _ = 5 / 2 * |d| * q * l ^ 2 * |h| ^ 3 := by rw [hu3]; field_simp

/-! ## Market-level facts for the exponential family -/

lemma eb_hasDerivAt_of_eq {f F : ℝ → ℝ} {F' p : ℝ} (hp : 0 < p) (heq : ∀ y, 0 < y → f y = F y)
    (hF : HasDerivAt F F' p) : HasDerivAt f F' p :=
  hF.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioi_mem_nhds hp) (fun y hy => heq y hy))

lemma eb_contOn {f f' : ℝ → ℝ} (hf : ∀ p, 0 < p → HasDerivAt f (f' p) p) :
    ContinuousOn f (Ioi 0) :=
  fun p hp => (hf p hp).continuousAt.continuousWithinAt

lemma eb_profit_eq (m : Market) (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i)
    (hlaw : ∀ i, m.law i = expMeasure (rate i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p) :
    profit m i p = eb_R (rate i) (m.population i) m.cost p := by
  unfold profit demand eb_R; rw [hlaw i, exp_demand (hrate i) hp]

lemma eb_demand_eq (m : Market) (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i)
    (hlaw : ∀ i, m.law i = expMeasure (rate i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p) :
    demand m i p = exp (-(rate i * p)) := by
  unfold demand; rw [hlaw i, exp_demand (hrate i) hp]

lemma eb_surplus_eq (m : Market) (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i)
    (hlaw : ∀ i, m.law i = expMeasure (rate i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p) :
    surplus m i p = exp (-(rate i * p)) / rate i := by
  unfold surplus; rw [hlaw i, exp_surplus (hrate i) hp]

lemma eb_nonbuyer_eq (m : Market) (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i)
    (hlaw : ∀ i, m.law i = expMeasure (rate i)) (i : Fin 2) {p : ℝ} (hp : 0 < p) :
    nonbuyer m i p = 1 / rate i - p / (exp (rate i * p) - 1) := by
  unfold nonbuyer; rw [hlaw i, exp_nonbuyer (hrate i) hp]

lemma eb_expneg_hasDeriv (l p : ℝ) :
    HasDerivAt (fun p => exp (-(l * p))) (-(l * exp (-(l * p)))) p := by
  have := ((hasDerivAt_id' p).const_mul l).neg.exp
  exact this.congr_deriv (by simp only [Pi.neg_apply]; ring)

lemma eb_nb_hasDeriv {l p : ℝ} (hl : 0 < l) (hp : 0 < p) :
    HasDerivAt (fun p => 1 / l - p / (exp (l * p) - 1)) (eb_h (l * p)) p := by
  have hne : exp (l * p) - 1 ≠ 0 := by
    have : 1 < exp (l * p) := one_lt_exp_iff.mpr (mul_pos hl hp)
    linarith
  have h1 := ((hasDerivAt_id' p).const_mul l).exp.sub_const 1
  have := (hasDerivAt_const p (1 / l)).sub ((hasDerivAt_id' p).div h1 hne)
  refine this.congr_deriv ?_
  unfold eb_h
  field_simp
  ring

lemma eb_BO_iff (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i)
    (hlaw : ∀ i, m.law i = expMeasure (rate i)) (b : Prices) :
    BaselineOptimal m b ↔ ∀ i, b i = m.cost + 1 / rate i := by
  have hps : ∀ i, 0 ≤ m.cost + 1 / rate i := fun i => by have := hrate i; positivity
  constructor
  · intro hb i
    obtain ⟨hb0, hmax⟩ := hb i
    by_contra hne
    have h1 := eb_R_lt m.cost (hrate i) (hd i) hne
    have h2 := hmax _ (hps i)
    rw [eb_profit_eq m rate hrate hlaw i (hps i), eb_profit_eq m rate hrate hlaw i hb0] at h2
    linarith
  · intro hb i
    refine ⟨hb i ▸ hps i, fun p hp => ?_⟩
    rw [eb_profit_eq m rate hrate hlaw i hp, eb_profit_eq m rate hrate hlaw i (hb i ▸ hps i), hb i]
    exact eb_R_le _ (hrate i) (hd i) p

lemma eb_lb {l : ℝ} (c : ℝ) (hl : 0 < l) : l * (c + 1 / l) = 1 + l * c := by
  field_simp; ring

lemma eb_X (d l q mm : Fin 2 → ℝ) (hd : ∀ i, 0 < d i) (hl : ∀ i, 0 < l i) (hq : ∀ i, 0 < q i) :
    d 0 * (-q 0) * mm 0 / (-(d 0 * l 0 * q 0)) - d 1 * (-q 1) * mm 1 / (-(d 1 * l 1 * q 1)) =
      mm 0 / l 0 - mm 1 / l 1 := by
  have := hd 0; have := hd 1; have := hl 0; have := hl 1; have := hq 0; have := hq 1
  field_simp

lemma eb_N_eq {l c : ℝ} (hl : 0 < l) (hc : 0 < c) :
    1 / l - (c + 1 / l) / (exp (l * (c + 1 / l)) - 1) = c * eb_g (1 + l * c) := by
  rw [eb_lb c hl]
  have hne : exp (1 + l * c) - 1 ≠ 0 := by
    have : 1 < exp (1 + l * c) := one_lt_exp_iff.mpr (by positivity)
    linarith
  unfold eb_g
  have : (1 + l * c - 1) = l * c := by ring
  rw [this]
  field_simp
  ring

lemma eb_n_eq {l c : ℝ} (hl : 0 < l) (hc : 0 < c) :
    eb_h (l * (c + 1 / l)) / l = c * eb_k (1 + l * c) := by
  rw [eb_lb c hl]
  unfold eb_k
  have : (1 + l * c - 1) = l * c := by ring
  rw [this]
  field_simp

lemma eb_sq_pos {G : ℝ} (hG : G ≠ 0) : 0 < G ^ 2 :=
  lt_of_le_of_ne (sq_nonneg G) (Ne.symm (pow_ne_zero 2 hG))

lemma eb_Dexp_pos (d l q mm : Fin 2 → ℝ) (G : ℝ) (hd : ∀ i, 0 < d i) (hl : ∀ i, 0 < l i)
    (hq : ∀ i, 0 < q i) (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0) (h : 0 < G * (mm 0 / l 0 - mm 1 / l 1)) :
    0 < d 0 * (-q 0) * ((-G / (mm 0 ^ 2 / (-(d 0 * l 0 * q 0)) + mm 1 ^ 2 / (-(d 1 * l 1 * q 1))))
        * mm 0 / (-(d 0 * l 0 * q 0))) +
      d 1 * (-q 1) * (-((-G / (mm 0 ^ 2 / (-(d 0 * l 0 * q 0)) + mm 1 ^ 2 / (-(d 1 * l 1 * q 1))))
        * mm 1 / (-(d 1 * l 1 * q 1)))) := by
  have hr : ∀ i, (fun i => -(d i * l i * q i)) i < 0 := fun i => by
    have := hd i; have := hl i; have := hq i
    simp only [neg_lt_zero]; positivity
  have := eb_D_pos d (fun i => -q i) mm (fun i => -(d i * l i * q i)) G hr hmm (by
    show 0 < G * (d 0 * (-q 0) * mm 0 / (-(d 0 * l 0 * q 0)) - d 1 * (-q 1) * mm 1 / (-(d 1 * l 1 * q 1)))
    rw [eb_X d l q mm hd hl hq]; exact h)
  exact this

lemma eb_Dexp_neg (d l q mm : Fin 2 → ℝ) (G : ℝ) (hd : ∀ i, 0 < d i) (hl : ∀ i, 0 < l i)
    (hq : ∀ i, 0 < q i) (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0) (h : G * (mm 0 / l 0 - mm 1 / l 1) < 0) :
    d 0 * (-q 0) * ((-G / (mm 0 ^ 2 / (-(d 0 * l 0 * q 0)) + mm 1 ^ 2 / (-(d 1 * l 1 * q 1))))
        * mm 0 / (-(d 0 * l 0 * q 0))) +
      d 1 * (-q 1) * (-((-G / (mm 0 ^ 2 / (-(d 0 * l 0 * q 0)) + mm 1 ^ 2 / (-(d 1 * l 1 * q 1))))
        * mm 1 / (-(d 1 * l 1 * q 1)))) < 0 := by
  have hr : ∀ i, (fun i => -(d i * l i * q i)) i < 0 := fun i => by
    have := hd i; have := hl i; have := hq i
    simp only [neg_lt_zero]; positivity
  have := eb_D_neg d (fun i => -q i) mm (fun i => -(d i * l i * q i)) G hr hmm (by
    show G * (d 0 * (-q 0) * mm 0 / (-(d 0 * l 0 * q 0)) - d 1 * (-q 1) * mm 1 / (-(d 1 * l 1 * q 1))) < 0
    rw [eb_X d l q mm hd hl hq]; exact h)
  exact this

lemma eb_surp_lt {c l0 l1 : ℝ} (hc : 0 ≤ c) (h0 : 0 < l0) (h01 : l0 < l1) :
    exp (-(1 + l1 * c)) / l1 < exp (-(1 + l0 * c)) / l0 := by
  have e : exp (-(1 + l1 * c)) ≤ exp (-(1 + l0 * c)) := exp_le_exp.mpr (by nlinarith)
  calc _ ≤ exp (-(1 + l0 * c)) / l1 := div_le_div_of_nonneg_right e (by linarith)
    _ < _ := div_lt_div_of_pos_left (exp_pos _) h0 h01

theorem goal_exp (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i) (hne : rate 0 ≠ rate 1)
    (hlaw : ∀ i, m.law i = expMeasure (rate i)) :
    (∃ b : Prices, BaselineOptimal m b) ∧
    ∀ b : Prices, BaselineOptimal m b →
      SensitivityClaim m b .price (fun D => 0 < D) ∧
      SensitivityClaim m b .nonbuyer (fun D => 0 < D) ∧
      SensitivityClaim m b .demand (fun D => D ≤ 0) ∧
      SensitivityClaim m b .surplus (fun D => D < 0) := by
  have hBO := eb_BO_iff m hd hc rate hrate hlaw
  refine ⟨⟨fun i => m.cost + 1 / rate i, (hBO _).2 (fun i => rfl)⟩, ?_⟩
  intro b hb
  have hbi := (hBO b).1 hb
  have hbpos : ∀ i, 0 < b i := fun i => by rw [hbi i]; have := hrate i; positivity
  have hlb : ∀ i, rate i * b i = 1 + rate i * m.cost := fun i => by
    rw [hbi i]; exact eb_lb _ (hrate i)
  have hopt : ∀ i, ∀ p, 0 ≤ p → profit m i p ≤ profit m i (b i) := fun i => (hb i).2
  have hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p →
      |p - b i| < ε := by
    intro ε hε
    obtain ⟨δ0, hδ0, H0⟩ := eb_R_loc m.cost (hrate 0) (hd 0) ε hε
    obtain ⟨δ1, hδ1, H1⟩ := eb_R_loc m.cost (hrate 1) (hd 1) ε hε
    refine ⟨min δ0 δ1, lt_min hδ0 hδ1, fun i p hp h => ?_⟩
    rw [eb_profit_eq m rate hrate hlaw i hp, eb_profit_eq m rate hrate hlaw i (hbpos i).le,
      hbi i] at h
    rw [hbi i]
    fin_cases i
    · exact H0 p (by have := min_le_left δ0 δ1; simp at h ⊢; linarith)
    · exact H1 p (by have := min_le_right δ0 δ1; simp at h ⊢; linarith)
  have hRd : ∀ i, ∀ p, 0 < p → HasDerivAt (profit m i)
      (m.population i * exp (-(rate i * p)) * (1 - rate i * (p - m.cost))) p :=
    fun i p hp => eb_hasDerivAt_of_eq hp (fun y hy => eb_profit_eq m rate hrate hlaw i hy.le)
      (eb_R_hasDeriv _ _ _ p)
  have hRc : ∀ i, ContinuousOn (profit m i) (Ioi 0) := fun i => eb_contOn (hRd i)
  set q : Fin 2 → ℝ := fun i => exp (-(rate i * b i)) with hq
  have hqpos : ∀ i, 0 < q i := fun i => exp_pos _
  have hr : ∀ i, (fun i => -(m.population i * rate i * q i)) i < 0 := fun i => by
    have := hd i; have := hrate i; have := hqpos i
    simp only [neg_lt_zero]; positivity
  have hRt : ∀ i, (fun h => profit m i (b i + h) - profit m i (b i) -
      (fun i => -(m.population i * rate i * q i)) i / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2) := by
    intro i
    have := eb_R_taylor (m.population i) m.cost (hrate i)
    rw [← hbi i] at this
    refine this.congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr (hbpos i)) (hbpos i)] with h hh
    have : 0 ≤ b i + h := by linarith [hh.1]
    rw [eb_profit_eq m rate hrate hlaw i this, eb_profit_eq m rate hrate hlaw i (hbpos i).le]
  have hSd' : ∀ i, ∀ p, 0 < p → HasDerivAt (surplus m i) (-exp (-(rate i * p))) p := by
    intro i p hp
    refine eb_hasDerivAt_of_eq hp (fun y hy => eb_surplus_eq m rate hrate hlaw i hy.le) ?_
    have := (eb_expneg_hasDeriv (rate i) p).div_const (rate i)
    refine this.congr_deriv ?_
    have := (hrate i).ne'
    field_simp
  have hSd : ∀ i, HasDerivAt (surplus m i) ((fun i => -q i) i) (b i) :=
    fun i => hSd' i (b i) (hbpos i)
  have hx : 0 < m.cost → ∀ i, 1 < 1 + rate i * m.cost := fun hcpos i => by
    have := hrate i; have : 0 < rate i * m.cost := by positivity
    linarith
  have hx01 : 0 < m.cost → 1 + rate 0 * m.cost ≠ 1 + rate 1 * m.cost := by
    intro hcpos h; apply hne
    have : rate 0 * m.cost = rate 1 * m.cost := by linarith
    exact mul_right_cancel₀ hcpos.ne' this
  have hqx : ∀ i, q i = exp (-(1 + rate i * m.cost)) := fun i => by
    simp only [hq]; rw [hlb i]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- price
    have hG : b 0 - b 1 ≠ 0 := by
      rw [hbi 0, hbi 1]; intro h; apply hne
      have : 1 / rate 0 = 1 / rate 1 := by linarith
      simpa using this
    refine eb_claim m b .price _ _ (fun _ => 1) _ hbpos hopt hloc hRc
      (fun i => continuous_id.continuousOn) hr hRt (fun i => hasDerivAt_id' (b i))
      (Or.inl one_ne_zero) hSd (sub_ne_zero.mp hG) ?_
    refine eb_Dexp_pos m.population rate q (fun _ => 1)
      (metricValue m .price 0 (b 0) - metricValue m .price 1 (b 1)) hd hrate hqpos (Or.inl one_ne_zero) ?_
    show 0 < (b 0 - b 1) * (1 / rate 0 - 1 / rate 1)
    have : b 0 - b 1 = 1 / rate 0 - 1 / rate 1 := by rw [hbi 0, hbi 1]; ring
    rw [this] at hG ⊢; exact mul_self_pos.mpr hG
  · -- nonbuyer
    have hNd : ∀ i, ∀ p, 0 < p →
        HasDerivAt (metricValue m .nonbuyer i) (eb_h (rate i * p)) p :=
      fun i p hp => eb_hasDerivAt_of_eq hp (fun y hy => eb_nonbuyer_eq m rate hrate hlaw i hy)
        (eb_nb_hasDeriv (hrate i) hp)
    have hsign : 0 < (metricValue m .nonbuyer 0 (b 0) - metricValue m .nonbuyer 1 (b 1)) *
        (eb_h (rate 0 * b 0) / rate 0 - eb_h (rate 1 * b 1) / rate 1) := by
      rcases hc.eq_or_lt with hzero | hcpos
      · -- c = 0: b i = 1 / rate i
        have hb1 : ∀ i, b i = 1 / rate i := fun i => by rw [hbi i, ← hzero, zero_add]
        have hl1 : ∀ i, rate i * b i = 1 := fun i => by
          rw [hb1 i]; field_simp [(hrate i).ne']
        have hv : ∀ i, metricValue m .nonbuyer i (b i) =
            (1 - 1 / (exp 1 - 1)) * (1 / rate i) := by
          intro i
          show nonbuyer m i (b i) = _
          rw [eb_nonbuyer_eq m rate hrate hlaw i (hbpos i), hl1 i, hb1 i]
          ring
        have he : 0 < 1 - 1 / (exp 1 - 1) := by
          have := exp_one_gt_d9
          rw [sub_pos, div_lt_one (by linarith)]; linarith
        have hh := eb_h_pos 1 one_pos
        have hG : 1 / rate 0 - 1 / rate 1 ≠ 0 := by
          intro h; apply hne
          have : 1 / rate 0 = 1 / rate 1 := by linarith
          simpa using this
        rw [hv 0, hv 1, hl1 0, hl1 1]
        have e : ((1 - 1 / (exp 1 - 1)) * (1 / rate 0) - (1 - 1 / (exp 1 - 1)) * (1 / rate 1)) *
            (eb_h 1 / rate 0 - eb_h 1 / rate 1) =
            ((1 - 1 / (exp 1 - 1)) * eb_h 1) * (1 / rate 0 - 1 / rate 1) ^ 2 := by ring
        rw [e]
        exact mul_pos (mul_pos he hh) (eb_sq_pos hG)
      have hv : ∀ i, metricValue m .nonbuyer i (b i) = m.cost * eb_g (1 + rate i * m.cost) := by
        intro i
        show nonbuyer m i (b i) = _
        rw [eb_nonbuyer_eq m rate hrate hlaw i (hbpos i), hbi i]
        exact eb_N_eq (hrate i) hcpos
      have hn : ∀ i, eb_h (rate i * b i) / rate i = m.cost * eb_k (1 + rate i * m.cost) := by
        intro i; rw [hbi i]; exact eb_n_eq (hrate i) hcpos
      have hgk : 0 < (eb_g (1 + rate 0 * m.cost) - eb_g (1 + rate 1 * m.cost)) *
          (eb_k (1 + rate 0 * m.cost) - eb_k (1 + rate 1 * m.cost)) := by
        have hx := hx hcpos
        rcases lt_or_gt_of_ne (hx01 hcpos) with h | h
        · have h1 := eb_g_anti (hx 0) (hx 1) h
          have h2 := eb_k_anti (hx 0) (hx 1) h
          exact mul_pos (by linarith) (by linarith)
        · have h1 := eb_g_anti (hx 1) (hx 0) h
          have h2 := eb_k_anti (hx 1) (hx 0) h
          exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
      rw [hv 0, hv 1, hn 0, hn 1]
      have : (m.cost * eb_g (1 + rate 0 * m.cost) - m.cost * eb_g (1 + rate 1 * m.cost)) *
          (m.cost * eb_k (1 + rate 0 * m.cost) - m.cost * eb_k (1 + rate 1 * m.cost)) =
          m.cost ^ 2 * ((eb_g (1 + rate 0 * m.cost) - eb_g (1 + rate 1 * m.cost)) *
          (eb_k (1 + rate 0 * m.cost) - eb_k (1 + rate 1 * m.cost))) := by ring
      rw [this]; positivity
    have hmm : (fun i => eb_h (rate i * b i)) 0 ≠ 0 ∨ (fun i => eb_h (rate i * b i)) 1 ≠ 0 :=
      Or.inl (eb_h_pos _ (mul_pos (hrate 0) (hbpos 0))).ne'
    have hgap : metricValue m .nonbuyer 0 (b 0) ≠ metricValue m .nonbuyer 1 (b 1) := by
      intro h
      rw [h, sub_self, zero_mul] at hsign; exact lt_irrefl _ hsign
    refine eb_claim m b .nonbuyer _ _ (fun i => eb_h (rate i * b i)) _ hbpos hopt hloc hRc
      (fun i => eb_contOn (hNd i)) hr hRt (fun i => hNd i (b i) (hbpos i)) hmm hSd hgap ?_
    refine eb_Dexp_pos m.population rate q (fun i => eb_h (rate i * b i))
      (metricValue m .nonbuyer 0 (b 0) - metricValue m .nonbuyer 1 (b 1)) hd hrate hqpos hmm hsign
  · -- demand
    have hDd : ∀ i, ∀ p, 0 < p →
        HasDerivAt (metricValue m .demand i) (-(rate i * exp (-(rate i * p)))) p :=
      fun i p hp => eb_hasDerivAt_of_eq hp (fun y hy => eb_demand_eq m rate hrate hlaw i hy.le)
        (eb_expneg_hasDeriv _ p)
    have hv : ∀ i, metricValue m .demand i (b i) = q i :=
      fun i => eb_demand_eq m rate hrate hlaw i (hbpos i).le
    rcases hc.eq_or_lt with hzero | hcpos
    · have huniq : ∀ b' : Prices, BaselineOptimal m b' → b' = b := fun b' hb' => by
        funext i; rw [(hBO b').1 hb' i, hbi i]
      refine wk_zero_gap m b .demand _ le_rfl hb huniq ?_
      rw [hv 0, hv 1, hqx 0, hqx 1, ← hzero, mul_zero, mul_zero]
    refine wk_mono m b .demand (fun D => D < 0) _ (fun D h => h.le) ?_
    have hG : q 0 - q 1 ≠ 0 := by
      rw [hqx 0, hqx 1]; intro h; apply hx01 hcpos
      have := exp_injective (sub_eq_zero.mp h)
      linarith
    have hmm : (fun i => -(rate i * q i)) 0 ≠ 0 ∨ (fun i => -(rate i * q i)) 1 ≠ 0 :=
      Or.inl (neg_ne_zero.mpr (mul_pos (hrate 0) (hqpos 0)).ne')
    have hgap : metricValue m .demand 0 (b 0) ≠ metricValue m .demand 1 (b 1) := by
      rw [hv 0, hv 1]; exact sub_ne_zero.mp hG
    refine eb_claim m b .demand _ _ (fun i => -(rate i * q i)) _ hbpos hopt hloc hRc
      (fun i => eb_contOn (hDd i)) hr hRt (fun i => hDd i (b i) (hbpos i)) hmm hSd hgap ?_
    refine eb_Dexp_neg m.population rate q (fun i => -(rate i * q i))
      (metricValue m .demand 0 (b 0) - metricValue m .demand 1 (b 1)) hd hrate hqpos hmm ?_
    show (metricValue m .demand 0 (b 0) - metricValue m .demand 1 (b 1)) *
      (-(rate 0 * q 0) / rate 0 - -(rate 1 * q 1) / rate 1) < 0
    rw [hv 0, hv 1]
    have e : -(rate 0 * q 0) / rate 0 - -(rate 1 * q 1) / rate 1 = -(q 0 - q 1) := by
      have := (hrate 0).ne'; have := (hrate 1).ne'
      field_simp; ring
    rw [e, mul_neg, neg_lt_zero]; exact mul_self_pos.mpr hG
  · -- surplus
    have hv : ∀ i, metricValue m .surplus i (b i) = q i / rate i :=
      fun i => eb_surplus_eq m rate hrate hlaw i (hbpos i).le
    have hG : q 0 / rate 0 - q 1 / rate 1 ≠ 0 := by
      rw [hqx 0, hqx 1]
      rcases lt_or_gt_of_ne hne with h | h
      · have := eb_surp_lt hc (hrate 0) h; linarith
      · have := eb_surp_lt hc (hrate 1) h; linarith
    have hmm : (fun i => -q i) 0 ≠ 0 ∨ (fun i => -q i) 1 ≠ 0 :=
      Or.inl (neg_ne_zero.mpr (hqpos 0).ne')
    have hgap : metricValue m .surplus 0 (b 0) ≠ metricValue m .surplus 1 (b 1) := by
      rw [hv 0, hv 1]; exact sub_ne_zero.mp hG
    refine eb_claim m b .surplus _ _ (fun i => -q i) _ hbpos hopt hloc hRc
      (fun i => eb_contOn (hSd' i)) hr hRt hSd hmm hSd hgap ?_
    refine eb_Dexp_neg m.population rate q (fun i => -q i)
      (metricValue m .surplus 0 (b 0) - metricValue m .surplus 1 (b 1)) hd hrate hqpos hmm ?_
    show (metricValue m .surplus 0 (b 0) - metricValue m .surplus 1 (b 1)) *
      (-q 0 / rate 0 - -q 1 / rate 1) < 0
    rw [hv 0, hv 1]
    have e : -q 0 / rate 0 - -q 1 / rate 1 = -(q 0 / rate 0 - q 1 / rate 1) := by ring
    rw [e, mul_neg, neg_lt_zero]; exact mul_self_pos.mpr hG


end CohenPriceFairness.LocalWelfare.Proofs

open MeasureTheory ProbabilityTheory
namespace CohenPriceFairness.LocalWelfare.Proofs

theorem theorem_2_weak (m : Market) (hd : ∀ i, 0 < m.population i)
    (hc : 0 ≤ m.cost)
    (hf : (∃ b : Fin 2 → ℝ, (∀ i, 0 < b i) ∧ b 0 ≠ b 1 ∧ m.cost < min (b 0) (b 1) ∧
            ∀ i, m.law i = uniformLaw (b i)) ∨
          (∃ rate : Fin 2 → ℝ, (∀ i, 0 < rate i) ∧ rate 0 ≠ rate 1 ∧
            ∀ i, m.law i = expMeasure (rate i))) :
    (∃ b : Prices, BaselineOptimal m b) ∧
    ∀ b : Prices, BaselineOptimal m b →
      SensitivityClaim m b .price (fun D => 0 ≤ D) ∧
      SensitivityClaim m b .nonbuyer (fun D => 0 ≤ D) ∧
      SensitivityClaim m b .demand (fun D => D ≤ 0) ∧
      SensitivityClaim m b .surplus (fun D => D ≤ 0) := by
  have H : (∃ b : Prices, BaselineOptimal m b) ∧
      ∀ b : Prices, BaselineOptimal m b →
        SensitivityClaim m b .price (fun D => 0 < D) ∧
        SensitivityClaim m b .nonbuyer (fun D => 0 < D) ∧
        SensitivityClaim m b .demand (fun D => D ≤ 0) ∧
        SensitivityClaim m b .surplus (fun D => D < 0) := by
    rcases hf with ⟨bb, hbb, hne, hcb, hlaw⟩ | ⟨rate, hrate, hne, hlaw⟩
    · exact goal_uniform m hd hc bb hbb hne hcb hlaw
    · exact goal_exp m hd hc rate hrate hne hlaw
  refine ⟨H.1, fun b hb => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := H.2 b hb
  exact ⟨wk_mono _ _ _ _ _ (fun D h => le_of_lt h) h1, wk_mono _ _ _ _ _ (fun D h => le_of_lt h) h2,
    h3, wk_mono _ _ _ _ _ (fun D h => le_of_lt h) h4⟩

end CohenPriceFairness.LocalWelfare.Proofs


open MeasureTheory ProbabilityTheory CohenPriceFairness.LocalWelfare

theorem solution (m : Market) (hd : ∀ i, 0 < m.population i)
    (hc : 0 ≤ m.cost)
    (hf : (∃ b : Fin 2 → ℝ, (∀ i, 0 < b i) ∧ b 0 ≠ b 1 ∧ m.cost < min (b 0) (b 1) ∧
            ∀ i, m.law i = uniformLaw (b i)) ∨
          (∃ rate : Fin 2 → ℝ, (∀ i, 0 < rate i) ∧ rate 0 ≠ rate 1 ∧
            ∀ i, m.law i = expMeasure (rate i))) :
    (∃ b : Prices, BaselineOptimal m b) ∧
    ∀ b : Prices, BaselineOptimal m b →
      SensitivityClaim m b .price (fun D => 0 ≤ D) ∧
      SensitivityClaim m b .nonbuyer (fun D => 0 ≤ D) ∧
      SensitivityClaim m b .demand (fun D => D ≤ 0) ∧
      SensitivityClaim m b .surplus (fun D => D ≤ 0) :=
  CohenPriceFairness.LocalWelfare.Proofs.theorem_2_weak m hd hc hf

#print axioms solution
