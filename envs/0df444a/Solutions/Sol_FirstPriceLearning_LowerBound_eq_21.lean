-- Prove2me | solution 1 for FirstPriceLearning.LowerBound.eq_21
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:40:32.131484+00:00
-- url     : https://prove2.me/submissions/ce4d3d29-9ecd-4cf7-be2b-9ec960a76011

import Mathlib
import Definitions.Def_FirstPriceLearning_LowerBound_Model
import Definitions.Def_FirstPriceLearning_LowerBound_TVDist
import Definitions.Def_FirstPriceLearning_LowerBound_TwoPointLaws

set_option autoImplicit false
open MeasureTheory InformationTheory ProbabilityTheory FirstPriceLearning.LowerBound

lemma twoPoint_prob (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsProbabilityMeasure (twoPointLaw p) := by
  constructor
  unfold twoPointLaw
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
    Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, Measure.dirac_apply_of_mem,
    Set.mem_univ, ENNReal.smul_def]
  rw [show ((p.toNNReal : ENNReal)) = ENNReal.ofReal p from rfl,
    show (((1 - p).toNNReal : ENNReal)) = ENNReal.ofReal (1 - p) from rfl, ← ENNReal.ofReal_add h0 (by linarith)]
  simp


lemma cdf_two (p b : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FirstPriceLearning.Stochastic.cdf (twoPointLaw p) b =
      (if 1 / 3 ≤ b then p else 0) + (if 2 / 3 ≤ b then 1 - p else 0) := by
  unfold FirstPriceLearning.Stochastic.cdf twoPointLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic]
  simp only [Set.indicator, Set.mem_Iic, Pi.one_apply, ENNReal.smul_def, smul_eq_mul]
  by_cases h1 : 1 / 3 ≤ b <;> by_cases h2 : 2 / 3 ≤ b <;> simp only [h1, h2, if_true, if_false, mul_one, mul_zero, add_zero, zero_add, ENNReal.toReal_add, ENNReal.coe_toReal, Real.coe_toNNReal _ hp0, Real.coe_toNNReal _ (sub_nonneg.mpr hp1), ENNReal.coe_ne_top, ne_eq, not_false_eq_true, ENNReal.toReal_zero]

lemma expR (p b : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FirstPriceLearning.Stochastic.expReward (twoPointLaw p) 1 b =
      (1 - b) * ((if 1 / 3 ≤ b then p else 0) + (if 2 / 3 ≤ b then 1 - p else 0)) := by
  unfold FirstPriceLearning.Stochastic.expReward
  rw [cdf_two p b hp0 hp1]

lemma maxima_aux (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) :
    IsGreatest ((fun b => FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b) '' Set.Icc (0 : ℝ) 1) ((1 + 2 * Δ) / 3) ∧
    IsGreatest ((fun b => FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b) '' Set.Icc (0 : ℝ) 1) (1 / 3) ∧
    IsGreatest ((fun b => FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b + FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b) '' Set.Icc (0 : ℝ) 1)
      (2 / 3) := by
  have hE1 : ∀ b, FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b =
      (1 - b) * ((if 1 / 3 ≤ b then 1 / 2 + Δ else 0) + (if 2 / 3 ≤ b then 1 - (1 / 2 + Δ) else 0)) :=
    fun b => expR _ b (by linarith) (by linarith)
  have hE2 : ∀ b, FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b =
      (1 - b) * ((if 1 / 3 ≤ b then 1 / 2 - Δ else 0) + (if 2 / 3 ≤ b then 1 - (1 / 2 - Δ) else 0)) :=
    fun b => expR _ b (by linarith) (by linarith)
  refine ⟨⟨⟨1 / 3, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩, ⟨⟨2 / 3, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩,
    ⟨⟨1 / 3, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩⟩
  · simp only [hE1]; norm_num; ring
  · rintro _ ⟨b, ⟨hb0, hb1⟩, rfl⟩
    simp only [hE1]
    split_ifs <;> nlinarith
  · simp only [hE2]; norm_num
  · rintro _ ⟨b, ⟨hb0, hb1⟩, rfl⟩
    simp only [hE2]
    split_ifs <;> nlinarith
  · simp only [hE1, hE2]; norm_num; ring
  · rintro _ ⟨b, ⟨hb0, hb1⟩, rfl⟩
    simp only [hE1, hE2]
    split_ifs <;> nlinarith

lemma sqrt_eq_mul_exp (L : ℝ) (hL : 0 < L) :
    Real.sqrt L = L * Real.exp (-(Real.log L) / 2) := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have h1 : Real.exp (-(Real.log L) / 2) = (Real.sqrt L)⁻¹ := by
    have : -(Real.log L) / 2 = -(Real.log (Real.sqrt L)) := by
      rw [Real.log_sqrt hL.le]; ring
    rw [this, Real.exp_neg, Real.exp_log hs]
  rw [h1]
  field_simp
  exact Real.sq_sqrt hL.le

lemma tangent_ineq (L m : ℝ) (hL : 0 ≤ L) :
    Real.exp m * (L - L * Real.log L / 2 - m * L) ≤ Real.sqrt L := by
  rcases hL.eq_or_lt with h0 | hpos
  · subst h0; simp
  · rw [sqrt_eq_mul_exp L hpos]
    set y := -(Real.log L) / 2 with hy
    have h1 : Real.exp y = Real.exp m * Real.exp (y - m) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 := Real.add_one_le_exp (y - m)
    have h3 : Real.exp m * (y - m + 1) ≤ Real.exp y := by
      rw [h1]; exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos m).le
    have h4 : L * (Real.exp m * (y - m + 1)) ≤ L * Real.exp y := mul_le_mul_of_nonneg_left h3 hL
    calc Real.exp m * (L - L * Real.log L / 2 - m * L) = L * (Real.exp m * (y - m + 1)) := by
          rw [hy]; ring
      _ ≤ L * Real.exp y := h4

lemma amgm_ineq (L t : ℝ) (hL : 0 ≤ L) (ht : 0 < t) :
    2 * Real.sqrt L ≤ t * min L 1 + max L 1 / t := by
  have hmM : min L 1 * max L 1 = L := by rw [min_mul_max]; ring
  have hm0 : 0 ≤ min L 1 := le_min hL zero_le_one
  have hM0 : 0 ≤ max L 1 := le_trans zero_le_one (le_max_right _ _)
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt L := ⟨_, rfl⟩
  rw [← hr]
  have hr2 : r ^ 2 = L := by rw [hr]; exact Real.sq_sqrt hL
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg L
  have key : 2 * r * t ≤ t ^ 2 * min L 1 + max L 1 := by
    rcases hm0.eq_or_lt with h0 | hpos
    · have : L = 0 := by rw [← hmM, ← h0]; ring
      have h2 : r ^ 2 = 0 := by rw [hr2]; assumption
      have : r = 0 := (pow_eq_zero_iff (by norm_num)).mp h2
      rw [this]; nlinarith
    · by_contra hc
      push_neg at hc
      have : min L 1 * (t ^ 2 * min L 1 + max L 1 - 2 * r * t) < 0 :=
        mul_neg_of_pos_of_neg hpos (by linarith)
      nlinarith [sq_nonneg (t * min L 1 - r)]
  rw [← sub_nonneg]
  have : t * min L 1 + max L 1 / t - 2 * r = (t ^ 2 * min L 1 + max L 1 - 2 * r * t) / t := by
    field_simp
  rw [this]
  apply div_nonneg _ ht.le
  linarith

lemma bh_abstract {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (L : Ω → ℝ) (hLm : Measurable L) (hL0 : ∀ x, 0 ≤ L x) (hLi : Integrable L Q)
    (hL1 : ∫ x, L x ∂Q = 1) (hK : Integrable (fun x => L x * Real.log (L x)) Q) :
    1 / 2 * Real.exp (-(∫ x, L x * Real.log (L x) ∂Q)) ≤ ∫ x, min (L x) 1 ∂Q := by
  set K := ∫ x, L x * Real.log (L x) ∂Q with hKdef
  set m : ℝ := -K / 2 with hm
  have hsm : Measurable (fun x => Real.sqrt (L x)) := hLm.sqrt
  have hLp1 : Integrable (fun x => L x + 1) Q := hLi.add (integrable_const (1 : ℝ))
  have hsi : Integrable (fun x => Real.sqrt (L x)) Q := by
    refine Integrable.mono' hLp1 hsm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt (hL0 x), Real.sqrt_nonneg (L x), sq_nonneg (Real.sqrt (L x) - 1)]
  set s := ∫ x, Real.sqrt (L x) ∂Q with hs
  have hlow : Integrable (fun x => Real.exp m * (L x - L x * Real.log (L x) / 2 - m * L x)) Q :=
    ((hLi.sub (hK.div_const 2)).sub (hLi.const_mul m)).const_mul _
  have hcalc : ∫ x, Real.exp m * (L x - L x * Real.log (L x) / 2 - m * L x) ∂Q = Real.exp m := by
    have i1 : Integrable (fun x => L x - L x * Real.log (L x) / 2) Q := hLi.sub (hK.div_const 2)
    have i2 : Integrable (fun x => m * L x) Q := hLi.const_mul m
    have i3 : Integrable (fun x => L x * Real.log (L x) / 2) Q := hK.div_const 2
    rw [integral_const_mul, integral_sub i1 i2, integral_sub hLi i3, integral_div,
      integral_const_mul, hL1]
    have : 1 - K / 2 - m * 1 = 1 := by rw [hm]; ring
    rw [this, mul_one]
  have hJ : Real.exp m ≤ s := by
    have := integral_mono hlow hsi (fun x => tangent_ineq (L x) m (hL0 x))
    rw [hcalc] at this
    exact this
  have hspos : 0 < s := lt_of_lt_of_le (Real.exp_pos m) hJ
  -- integrability of min and max
  have hmin_m : Measurable (fun x => min (L x) 1) := hLm.min measurable_const
  have hmax_m : Measurable (fun x => max (L x) 1) := hLm.max measurable_const
  have hmin_i : Integrable (fun x => min (L x) 1) Q :=
    Integrable.of_bound hmin_m.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hL0 x) zero_le_one)]; exact min_le_right _ _)
  have hmax_i : Integrable (fun x => max (L x) 1) Q := by
    refine Integrable.mono' hLp1 hmax_m.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (le_max_right _ _))]
    have := hL0 x
    rcases le_total (L x) 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  set A := ∫ x, min (L x) 1 ∂Q with hA
  have hB : ∫ x, max (L x) 1 ∂Q ≤ 2 := by
    have : ∫ x, max (L x) 1 ∂Q ≤ ∫ x, (L x + 1) ∂Q :=
      integral_mono hmax_i hLp1 (fun x => by
        have := hL0 x
        rcases le_total (L x) 1 with h | h
        · simp only [max_eq_right h]; linarith
        · simp only [max_eq_left h]; linarith)
    rw [integral_add hLi (integrable_const _), hL1] at this
    simp at this
    linarith
  have ht : 0 < 2 / s := by positivity
  have iA : Integrable (fun x => 2 / s * min (L x) 1) Q := hmin_i.const_mul _
  have iB : Integrable (fun x => max (L x) 1 / (2 / s)) Q := hmax_i.div_const _
  have hint : ∫ x, 2 * Real.sqrt (L x) ∂Q ≤
      ∫ x, (2 / s * min (L x) 1 + max (L x) 1 / (2 / s)) ∂Q :=
    integral_mono (hsi.const_mul 2) (iA.add iB) (fun x => amgm_ineq (L x) (2 / s) (hL0 x) ht)
  rw [integral_const_mul, integral_add iA iB, integral_const_mul, integral_div] at hint
  have h2 : 2 * s ≤ 2 / s * A + (∫ x, max (L x) 1 ∂Q) / (2 / s) := hint
  have h3 : (∫ x, max (L x) 1 ∂Q) / (2 / s) ≤ s := by
    rw [div_le_iff₀ ht]
    have : s * (2 / s) = 2 := by field_simp
    rw [this]; exact hB
  have h4 : s ≤ 2 / s * A := by linarith
  have h5 : s ^ 2 ≤ 2 * A := by
    have : s * s ≤ 2 / s * A * s := mul_le_mul_of_nonneg_right h4 hspos.le
    have e : 2 / s * A * s = 2 * A := by field_simp
    nlinarith
  have h6 : Real.exp (-K) = Real.exp m * Real.exp m := by
    rw [← Real.exp_add]; congr 1; rw [hm]; ring
  have h7 : Real.exp m * Real.exp m ≤ s ^ 2 := by
    rw [sq]; exact mul_self_le_mul_self (Real.exp_pos m).le hJ
  rw [h6]
  linarith

lemma tvDist_comm {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) :
    tvDist P Q = tvDist Q P := by
  unfold tvDist
  rw [add_comm Q P]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x => abs_sub_comm _ _)

lemma one_sub_tv {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    1 - tvDist P Q = ∫ ω, min (P.rnDeriv (P + Q) ω).toReal (Q.rnDeriv (P + Q) ω).toReal ∂(P + Q) := by
  have hPν : P ≪ P + Q := Measure.absolutelyContinuous_of_le (Measure.le_add_right (le_refl P))
  have hQν : Q ≪ P + Q := Measure.absolutelyContinuous_of_le (Measure.le_add_left (le_refl Q))
  have hp : Integrable (fun ω => (P.rnDeriv (P + Q) ω).toReal) (P + Q) :=
    Measure.integrable_toReal_rnDeriv
  have hq : Integrable (fun ω => (Q.rnDeriv (P + Q) ω).toReal) (P + Q) :=
    Measure.integrable_toReal_rnDeriv
  have hp1 : ∫ ω, (P.rnDeriv (P + Q) ω).toReal ∂(P + Q) = 1 := by
    rw [Measure.integral_toReal_rnDeriv hPν]; simp
  have hq1 : ∫ ω, (Q.rnDeriv (P + Q) ω).toReal ∂(P + Q) = 1 := by
    rw [Measure.integral_toReal_rnDeriv hQν]; simp
  have hmin : Integrable (fun ω => min (P.rnDeriv (P + Q) ω).toReal (Q.rnDeriv (P + Q) ω).toReal)
      (P + Q) := by
    refine Integrable.mono' hp
      (((Measure.measurable_rnDeriv P (P + Q)).ennreal_toReal.min
        (Measure.measurable_rnDeriv Q (P + Q)).ennreal_toReal).aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
    exact min_le_left _ _
  have habs : ∀ ω, |(P.rnDeriv (P + Q) ω).toReal - (Q.rnDeriv (P + Q) ω).toReal| =
      (P.rnDeriv (P + Q) ω).toReal + (Q.rnDeriv (P + Q) ω).toReal
        - 2 * min (P.rnDeriv (P + Q) ω).toReal (Q.rnDeriv (P + Q) ω).toReal := by
    intro ω
    rcases le_total (P.rnDeriv (P + Q) ω).toReal (Q.rnDeriv (P + Q) ω).toReal with h | h
    · rw [abs_of_nonpos (by linarith), min_eq_left h]; ring
    · rw [abs_of_nonneg (by linarith), min_eq_right h]; ring
  unfold tvDist
  simp_rw [habs]
  have hpq : Integrable (fun ω => (P.rnDeriv (P + Q) ω).toReal + (Q.rnDeriv (P + Q) ω).toReal)
      (P + Q) := hp.add hq
  have hmin2 : Integrable (fun ω => 2 * min (P.rnDeriv (P + Q) ω).toReal
      (Q.rnDeriv (P + Q) ω).toReal) (P + Q) := hmin.const_mul 2
  rw [integral_sub hpq hmin2, integral_add hp hq, hp1, hq1, integral_const_mul]
  ring

lemma bh_one {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hK : klDiv P Q ≠ ⊤) :
    1 / 2 * Real.exp (-(klDiv P Q).toReal) ≤ 1 - tvDist P Q := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hK
  have hQν : Q ≪ P + Q := Measure.absolutelyContinuous_of_le (Measure.le_add_left (le_refl Q))
  set L : Ω → ℝ := fun x => (P.rnDeriv Q x).toReal with hL
  have hLm : Measurable L := (Measure.measurable_rnDeriv P Q).ennreal_toReal
  have hL0 : ∀ x, 0 ≤ L x := fun x => ENNReal.toReal_nonneg
  have hLi : Integrable L Q := Measure.integrable_toReal_rnDeriv
  have hL1 : ∫ x, L x ∂Q = 1 := by rw [hL, Measure.integral_toReal_rnDeriv hac]; simp
  have hK' : Integrable (fun x => L x * Real.log (L x)) Q :=
    (integrable_toReal_rnDeriv_mul_iff hac).mpr hint
  have hKeq : (klDiv P Q).toReal = ∫ x, L x * Real.log (L x) ∂Q := by
    rw [toReal_klDiv hac hint]
    have := integral_toReal_rnDeriv_mul hac (f := llr P Q)
    simp only [llr] at this
    rw [hL]; simp only
    rw [this]
    simp [llr]
  have habs := bh_abstract Q L hLm hL0 hLi hL1 hK'
  rw [hKeq]
  refine habs.trans (le_of_eq ?_)
  rw [one_sub_tv P Q]
  have hmain : ∀ᵐ ω ∂(P + Q), min (P.rnDeriv (P + Q) ω).toReal (Q.rnDeriv (P + Q) ω).toReal =
      (Q.rnDeriv (P + Q) ω).toReal * min (L ω) 1 := by
    filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := P + Q) hac] with ω h
    have h' : (P.rnDeriv (P + Q) ω).toReal = L ω * (Q.rnDeriv (P + Q) ω).toReal := by
      rw [← h]; simp [hL, ENNReal.toReal_mul]
    rw [h']
    have hq0 : 0 ≤ (Q.rnDeriv (P + Q) ω).toReal := ENNReal.toReal_nonneg
    rcases le_total (L ω) 1 with h1 | h1
    · rw [min_eq_left h1, min_eq_left (by nlinarith)]; ring
    · rw [min_eq_right h1, min_eq_right (by nlinarith)]; ring
  rw [integral_congr_ae hmain]
  exact (integral_toReal_rnDeriv_mul hQν (f := fun x => min (L x) 1)).symm

lemma one_sub_tv_nonneg {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : 0 ≤ 1 - tvDist P Q := by
  rw [one_sub_tv]
  exact integral_nonneg fun ω => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg

lemma bh_sym {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    (if klDiv P Q = ⊤ ∨ klDiv Q P = ⊤ then (0 : ℝ)
      else 1 / 2 * Real.exp (-((klDiv P Q).toReal + (klDiv Q P).toReal) / 2)) ≤
      1 - tvDist P Q := by
  split_ifs with h
  · exact one_sub_tv_nonneg P Q
  · push_neg at h
    obtain ⟨h1, h2⟩ := h
    have k1 : 0 ≤ (klDiv P Q).toReal := ENNReal.toReal_nonneg
    have k2 : 0 ≤ (klDiv Q P).toReal := ENNReal.toReal_nonneg
    rcases le_total (klDiv P Q).toReal (klDiv Q P).toReal with h | h
    · refine le_trans ?_ (bh_one P Q h1)
      gcongr
      linarith
    · refine le_trans ?_ (tvDist_comm P Q ▸ bh_one Q P h2)
      gcongr
      linarith

lemma sup_of_greatest (f : ℝ → ℝ) (v : ℝ) (h : IsGreatest (f '' Set.Icc (0 : ℝ) 1) v) :
    (⨆ b : Set.Icc (0 : ℝ) 1, f b) = v := by
  rw [← sSup_image']
  exact h.csSup_eq

lemma eq20_aux (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) :
    (∀ bt ∈ Set.Icc (0 : ℝ) 1,
      FirstPriceLearning.Stochastic.oracle (lawG1 Δ) 1 + FirstPriceLearning.Stochastic.oracle (lawG2 Δ) 1
          - (⨆ b : Set.Icc (0 : ℝ) 1, (FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b + FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b)) ≤
        (FirstPriceLearning.Stochastic.oracle (lawG1 Δ) 1 - FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 bt)
          + (FirstPriceLearning.Stochastic.oracle (lawG2 Δ) 1 - FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 bt)) ∧
    FirstPriceLearning.Stochastic.oracle (lawG1 Δ) 1 + FirstPriceLearning.Stochastic.oracle (lawG2 Δ) 1
        - (⨆ b : Set.Icc (0 : ℝ) 1, (FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b + FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b)) =
      2 * Δ / 3 := by
  obtain ⟨h1, h2, h3⟩ := maxima_aux Δ hΔ0 hΔ1
  have e1 : FirstPriceLearning.Stochastic.oracle (lawG1 Δ) 1 = (1 + 2 * Δ) / 3 :=
    sup_of_greatest (fun b => FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b) _ h1
  have e2 : FirstPriceLearning.Stochastic.oracle (lawG2 Δ) 1 = 1 / 3 :=
    sup_of_greatest (fun b => FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b) _ h2
  have e3 : (⨆ b : Set.Icc (0 : ℝ) 1, (FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b + FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b)) = 2 / 3 :=
    sup_of_greatest (fun b => FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b + FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b) _ h3
  rw [e1, e2, e3]
  refine ⟨fun bt hbt => ?_, by ring⟩
  have := h3.2 ⟨bt, hbt, rfl⟩
  simp only at this
  linarith

/-- facts about the instantaneous regrets -/
lemma reg_facts (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (0 ≤ FirstPriceLearning.Stochastic.oracle (lawG1 Δ) 1 - FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b ∧
      FirstPriceLearning.Stochastic.oracle (lawG1 Δ) 1 - FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b ≤ 1) ∧
    (0 ≤ FirstPriceLearning.Stochastic.oracle (lawG2 Δ) 1 - FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b ∧
      FirstPriceLearning.Stochastic.oracle (lawG2 Δ) 1 - FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b ≤ 1) ∧
    2 * Δ / 3 ≤ (FirstPriceLearning.Stochastic.oracle (lawG1 Δ) 1 - FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b)
      + (FirstPriceLearning.Stochastic.oracle (lawG2 Δ) 1 - FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b) := by
  obtain ⟨h1, h2, h3⟩ := maxima_aux Δ hΔ0 hΔ1
  have e1 : FirstPriceLearning.Stochastic.oracle (lawG1 Δ) 1 = (1 + 2 * Δ) / 3 :=
    sup_of_greatest (fun b => FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b) _ h1
  have e2 : FirstPriceLearning.Stochastic.oracle (lawG2 Δ) 1 = 1 / 3 :=
    sup_of_greatest (fun b => FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b) _ h2
  have u1 := h1.2 ⟨b, hb, rfl⟩
  have u2 := h2.2 ⟨b, hb, rfl⟩
  have n1 : 0 ≤ FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b := by
    unfold FirstPriceLearning.Stochastic.expReward FirstPriceLearning.Stochastic.cdf
    exact mul_nonneg (by linarith [hb.2]) ENNReal.toReal_nonneg
  have n2 : 0 ≤ FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b := by
    unfold FirstPriceLearning.Stochastic.expReward FirstPriceLearning.Stochastic.cdf
    exact mul_nonneg (by linarith [hb.2]) ENNReal.toReal_nonneg
  simp only at u1 u2
  have := (eq20_aux Δ hΔ0 hΔ1).1 b hb
  rw [(eq20_aux Δ hΔ0 hΔ1).2] at this
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, this⟩
  · rw [e1]; linarith
  · rw [e1]; linarith
  · rw [e2]; linarith
  · rw [e2]; linarith

lemma cdf_meas (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measurable (fun b => FirstPriceLearning.Stochastic.expReward μ 1 b) := by
  unfold FirstPriceLearning.Stochastic.expReward
  refine (measurable_const.sub measurable_id).mul ?_
  have : Monotone (FirstPriceLearning.Stochastic.cdf μ) := fun a b hab =>
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr hab))
  exact this.measurable

lemma core_ineq {Ω : Type*} [MeasurableSpace Ω] (P1 P2 : Measure Ω) [IsProbabilityMeasure P1]
    [IsProbabilityMeasure P2] (g1 g2 : Ω → ℝ) (hm1 : Measurable g1) (hm2 : Measurable g2)
    (h1 : ∀ ω, 0 ≤ g1 ω) (h2 : ∀ ω, 0 ≤ g2 ω) (hb1 : ∀ ω, g1 ω ≤ 1) (hb2 : ∀ ω, g2 ω ≤ 1)
    (c : ℝ) (hc : ∀ ω, c ≤ g1 ω + g2 ω) :
    c * (1 - tvDist P1 P2) ≤ ∫ ω, g1 ω ∂P1 + ∫ ω, g2 ω ∂P2 := by
  have hPν : P1 ≪ P1 + P2 := Measure.absolutelyContinuous_of_le (Measure.le_add_right (le_refl P1))
  have hQν : P2 ≪ P1 + P2 := Measure.absolutelyContinuous_of_le (Measure.le_add_left (le_refl P2))
  set p : Ω → ℝ := fun ω => (P1.rnDeriv (P1 + P2) ω).toReal with hp
  set q : Ω → ℝ := fun ω => (P2.rnDeriv (P1 + P2) ω).toReal with hq
  have hpm : Measurable p := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hqm : Measurable q := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hp0 : ∀ ω, 0 ≤ p ω := fun ω => ENNReal.toReal_nonneg
  have hq0 : ∀ ω, 0 ≤ q ω := fun ω => ENNReal.toReal_nonneg
  have hpi : Integrable p (P1 + P2) := Measure.integrable_toReal_rnDeriv
  have hqi : Integrable q (P1 + P2) := Measure.integrable_toReal_rnDeriv
  have i1 : Integrable (fun ω => p ω * g1 ω) (P1 + P2) := by
    refine Integrable.mono' hpi (hpm.mul hm1).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp0 ω) (h1 ω))]
    nlinarith [hp0 ω, hb1 ω]
  have i2 : Integrable (fun ω => q ω * g2 ω) (P1 + P2) := by
    refine Integrable.mono' hqi (hqm.mul hm2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 ω) (h2 ω))]
    nlinarith [hq0 ω, hb2 ω]
  have e1 : ∫ ω, g1 ω ∂P1 = ∫ ω, p ω * g1 ω ∂(P1 + P2) :=
    (integral_toReal_rnDeriv_mul hPν (f := g1)).symm
  have e2 : ∫ ω, g2 ω ∂P2 = ∫ ω, q ω * g2 ω ∂(P1 + P2) :=
    (integral_toReal_rnDeriv_mul hQν (f := g2)).symm
  have hmin : Integrable (fun ω => min (p ω) (q ω)) (P1 + P2) := by
    refine Integrable.mono' hpi ((hpm.min hqm).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp0 ω) (hq0 ω))]
    exact min_le_left _ _
  have hmono : ∫ ω, c * min (p ω) (q ω) ∂(P1 + P2) ≤ ∫ ω, (p ω * g1 ω + q ω * g2 ω) ∂(P1 + P2) := by
    refine integral_mono (hmin.const_mul c) (i1.add i2) (fun ω => ?_)
    have hm0 : 0 ≤ min (p ω) (q ω) := le_min (hp0 ω) (hq0 ω)
    have a1 : min (p ω) (q ω) * g1 ω ≤ p ω * g1 ω :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (h1 ω)
    have a2 : min (p ω) (q ω) * g2 ω ≤ q ω * g2 ω :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (h2 ω)
    have a3 : c * min (p ω) (q ω) ≤ (g1 ω + g2 ω) * min (p ω) (q ω) :=
      mul_le_mul_of_nonneg_right (hc ω) hm0
    nlinarith
  rw [e1, e2, ← integral_add i1 i2]
  have hov : 1 - tvDist P1 P2 = ∫ ω, min (p ω) (q ω) ∂(P1 + P2) := one_sub_tv P1 P2
  rw [integral_const_mul, ← hov] at hmono
  exact hmono

lemma bid_joint_meas {T : ℕ} {U : Type} [MeasurableSpace U] (π : FullInfoPolicy T U) (t : Fin T) :
    Measurable (fun p : U × (Fin T → ℝ) => π.realizedBid t p.1 p.2) := by
  unfold FullInfoPolicy.realizedBid
  exact (π.measurable_bid t).comp (measurable_fst.prodMk
    (measurable_pi_lambda _ fun s => (measurable_pi_apply _).comp measurable_snd))

lemma per_round {T : ℕ} {U : Type} [MeasurableSpace U] (π : FullInfoPolicy T U) (Δ : ℝ)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) (t : Fin T) :
    2 * Δ / 3 * (1 - tvDist (Measure.pi fun _ : Fin T => lawG1 Δ) (Measure.pi fun _ : Fin T => lawG2 Δ)) ≤
      (∫ p, (FirstPriceLearning.Stochastic.oracle (lawG1 Δ) 1 -
        FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 (π.realizedBid t p.1 p.2))
          ∂(π.μU.prod (Measure.pi fun _ : Fin T => lawG1 Δ))) +
      (∫ p, (FirstPriceLearning.Stochastic.oracle (lawG2 Δ) 1 -
        FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 (π.realizedBid t p.1 p.2))
          ∂(π.μU.prod (Measure.pi fun _ : Fin T => lawG2 Δ))) := by
  haveI := π.isProb
  haveI : IsProbabilityMeasure (lawG1 Δ) := twoPoint_prob _ (by linarith) (by linarith)
  haveI : IsProbabilityMeasure (lawG2 Δ) := twoPoint_prob _ (by linarith) (by linarith)
  set P1 : Measure (Fin T → ℝ) := Measure.pi fun _ : Fin T => lawG1 Δ with hP1
  set P2 : Measure (Fin T → ℝ) := Measure.pi fun _ : Fin T => lawG2 Δ with hP2
  set F1 : U × (Fin T → ℝ) → ℝ := fun p => FirstPriceLearning.Stochastic.oracle (lawG1 Δ) 1 -
        FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 (π.realizedBid t p.1 p.2) with hF1
  set F2 : U × (Fin T → ℝ) → ℝ := fun p => FirstPriceLearning.Stochastic.oracle (lawG2 Δ) 1 -
        FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 (π.realizedBid t p.1 p.2) with hF2
  have hbid : ∀ p : U × (Fin T → ℝ), π.realizedBid t p.1 p.2 ∈ Set.Icc (0 : ℝ) 1 :=
    fun p => π.bid_mem _ _ _
  have hF1m : Measurable F1 := measurable_const.sub ((cdf_meas _).comp (bid_joint_meas π t))
  have hF2m : Measurable F2 := measurable_const.sub ((cdf_meas _).comp (bid_joint_meas π t))
  have hI1 : Integrable F1 (π.μU.prod P1) :=
    Integrable.of_bound hF1m.aestronglyMeasurable 1 (ae_of_all _ fun p => by
      have := (reg_facts Δ hΔ0 hΔ1 _ (hbid p)).1
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)
  have hI2 : Integrable F2 (π.μU.prod P2) :=
    Integrable.of_bound hF2m.aestronglyMeasurable 1 (ae_of_all _ fun p => by
      have := (reg_facts Δ hΔ0 hΔ1 _ (hbid p)).2.1
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)
  show 2 * Δ / 3 * (1 - tvDist P1 P2) ≤ ∫ p, F1 p ∂(π.μU.prod P1) + ∫ p, F2 p ∂(π.μU.prod P2)
  rw [integral_prod _ hI1, integral_prod _ hI2]
  have hcore : ∀ u : U, 2 * Δ / 3 * (1 - tvDist P1 P2) ≤
      ∫ m, F1 (u, m) ∂P1 + ∫ m, F2 (u, m) ∂P2 := by
    intro u
    refine core_ineq P1 P2 (fun m => F1 (u, m)) (fun m => F2 (u, m))
      (hF1m.comp measurable_prodMk_left) (hF2m.comp measurable_prodMk_left) ?_ ?_ ?_ ?_ _ ?_
    · intro m; exact ((reg_facts Δ hΔ0 hΔ1 _ (hbid (u, m))).1).1
    · intro m; exact ((reg_facts Δ hΔ0 hΔ1 _ (hbid (u, m))).2.1).1
    · intro m; exact ((reg_facts Δ hΔ0 hΔ1 _ (hbid (u, m))).1).2
    · intro m; exact ((reg_facts Δ hΔ0 hΔ1 _ (hbid (u, m))).2.1).2
    · intro m; exact (reg_facts Δ hΔ0 hΔ1 _ (hbid (u, m))).2.2
  have a1 : Integrable (fun u => ∫ m, F1 (u, m) ∂P1) π.μU := hI1.integral_prod_left
  have a2 : Integrable (fun u => ∫ m, F2 (u, m) ∂P2) π.μU := hI2.integral_prod_left
  rw [← integral_add a1 a2]
  calc 2 * Δ / 3 * (1 - tvDist P1 P2) = ∫ u, 2 * Δ / 3 * (1 - tvDist P1 P2) ∂π.μU := by simp
    _ ≤ _ := integral_mono (integrable_const _) (a1.add a2) hcore

lemma er_eq {T : ℕ} {U : Type} [MeasurableSpace U] (π : FullInfoPolicy T U) (μG : Measure ℝ)
    [IsProbabilityMeasure μG] (hb : ∀ t : Fin T, ∀ p : U × (Fin T → ℝ),
      0 ≤ FirstPriceLearning.Stochastic.oracle μG 1 - FirstPriceLearning.Stochastic.expReward μG 1 (π.realizedBid t p.1 p.2) ∧
      FirstPriceLearning.Stochastic.oracle μG 1 - FirstPriceLearning.Stochastic.expReward μG 1 (π.realizedBid t p.1 p.2) ≤ 1) :
    expectedRegret π μG = ∑ t : Fin T, ∫ p, (FirstPriceLearning.Stochastic.oracle μG 1 -
        FirstPriceLearning.Stochastic.expReward μG 1 (π.realizedBid t p.1 p.2))
          ∂(π.μU.prod (Measure.pi fun _ : Fin T => μG)) := by
  haveI := π.isProb
  unfold expectedRegret
  simp only [FirstPriceLearning.Adversarial.regret]
  rw [integral_finset_sum]
  intro t _
  refine Integrable.of_bound ?_ 1 (ae_of_all _ fun p => ?_)
  · exact (measurable_const.sub ((cdf_meas _).comp (bid_joint_meas π t))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (hb t p).1]; exact (hb t p).2

theorem solution {T : ℕ} {U : Type} [MeasurableSpace U] (π : FullInfoPolicy T U)
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) :
    Δ * T / 3 * (1 - tvDist (Measure.pi fun _ : Fin T => lawG1 Δ)
        (Measure.pi fun _ : Fin T => lawG2 Δ)) ≤
      1 / 2 * expectedRegret π (lawG1 Δ) + 1 / 2 * expectedRegret π (lawG2 Δ) := by
  haveI : IsProbabilityMeasure (lawG1 Δ) := twoPoint_prob _ (by linarith) (by linarith)
  haveI : IsProbabilityMeasure (lawG2 Δ) := twoPoint_prob _ (by linarith) (by linarith)
  have hbid : ∀ (t : Fin T) (p : U × (Fin T → ℝ)), π.realizedBid t p.1 p.2 ∈ Set.Icc (0 : ℝ) 1 :=
    fun t p => π.bid_mem _ _ _
  rw [er_eq π (lawG1 Δ) (fun t p => (reg_facts Δ hΔ0 hΔ1 _ (hbid t p)).1),
    er_eq π (lawG2 Δ) (fun t p => (reg_facts Δ hΔ0 hΔ1 _ (hbid t p)).2.1)]
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin T))) =>
    per_round π Δ hΔ0 hΔ1 t)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  nlinarith [hsum]
