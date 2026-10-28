-- Prove2me | solution 2 for FirstPriceLearning.LowerBound.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:19:53.778412+00:00
-- url     : https://prove2.me/submissions/79c8f6f5-3968-4fb4-b930-0c03c8f54434

import Mathlib
import Definitions.Def_FirstPriceLearning_LowerBound_Model
import Definitions.Def_FirstPriceLearning_LowerBound_TVDist
import Definitions.Def_FirstPriceLearning_LowerBound_TwoPointLaws
import Theorems.Thm_FirstPriceLearning_LowerBound_eq_21
import Theorems.Thm_FirstPriceLearning_LowerBound_kl_display

-- carved verbatim out of submission 4dbaa436-5cd4-4fab-9d2e-ef70cca7c3ee, lines 701-739

section
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

lemma eq22 (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) :
    1 / 2 * Real.exp (-(32 * T * Δ ^ 2)) ≤
      1 - tvDist (Measure.pi fun _ : Fin T => lawG1 Δ) (Measure.pi fun _ : Fin T => lawG2 Δ) := by
  haveI : IsProbabilityMeasure (lawG1 Δ) := twoPoint_prob _ (by linarith) (by linarith)
  haveI : IsProbabilityMeasure (lawG2 Δ) := twoPoint_prob _ (by linarith) (by linarith)
  obtain ⟨_, _, h3, _⟩ := FirstPriceLearning.LowerBound.kl_display T Δ hΔ0 hΔ1
  have hne : klDiv (Measure.pi fun _ : Fin T => lawG1 Δ) (Measure.pi fun _ : Fin T => lawG2 Δ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h3
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
  rw [ENNReal.toReal_ofReal (by positivity)] at hle
  refine le_trans ?_ (bh_one _ _ hne)
  gcongr

lemma supp_two (p : ℝ) : twoPointLaw p (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  unfold twoPointLaw
  have hs : MeasurableSet (Set.Icc (0 : ℝ) 1)ᶜ := measurableSet_Icc.compl
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs, ENNReal.smul_def,
    smul_eq_mul]
  have h1 : (1 / 3 : ℝ) ∉ (Set.Icc (0 : ℝ) 1)ᶜ := by
    simp only [Set.mem_compl_iff, not_not, Set.mem_Icc]; constructor <;> norm_num
  have h2 : (2 / 3 : ℝ) ∉ (Set.Icc (0 : ℝ) 1)ᶜ := by
    simp only [Set.mem_compl_iff, not_not, Set.mem_Icc]; constructor <;> norm_num
  classical
  simp only [Set.indicator_apply, if_neg h1, if_neg h2]
  simp

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ T : ℕ, 1 ≤ T → ∀ (U : Type) [MeasurableSpace U] (π : FullInfoPolicy T U),
        ∃ μG : Measure ℝ, IsProbabilityMeasure μG ∧ μG (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
          c * Real.sqrt T ≤ expectedRegret π μG := by
  refine ⟨Real.exp (-(1 / 2)) / 48, by positivity, ?_⟩
  intro T hT U _ π
  have hT0 : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hsq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hsq2 : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT0.le
  have hsq1 : 1 ≤ Real.sqrt T := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hT)
  set Δ : ℝ := 1 / (8 * Real.sqrt T) with hΔ
  have hΔ0 : 0 < Δ := by positivity
  have hΔ1 : Δ < 1 / 4 := by
    rw [hΔ, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hTΔ : (T : ℝ) * Δ ^ 2 = 1 / 64 := by
    rw [hΔ, div_pow, mul_pow, hsq2]; field_simp; ring
  have h21 := FirstPriceLearning.LowerBound.eq_21 π Δ hΔ0 hΔ1
  have h22 := eq22 T Δ hΔ0 hΔ1
  have hex : 32 * (T : ℝ) * Δ ^ 2 = 1 / 2 := by nlinarith [hTΔ]
  rw [hex] at h22
  have hΔT : Δ * T = Real.sqrt T / 8 := by
    rw [hΔ]; field_simp; nlinarith [hsq2]
  have hlow : Real.exp (-(1 / 2)) / 48 * Real.sqrt T ≤
      1 / 2 * expectedRegret π (lawG1 Δ) + 1 / 2 * expectedRegret π (lawG2 Δ) := by
    refine le_trans ?_ h21
    have : Δ * T / 3 * (1 / 2 * Real.exp (-(1 / 2))) ≤ Δ * T / 3 *
        (1 - tvDist (Measure.pi fun _ : Fin T => lawG1 Δ) (Measure.pi fun _ : Fin T => lawG2 Δ)) := by
      apply mul_le_mul_of_nonneg_left h22; positivity
    refine le_trans (le_of_eq ?_) this
    rw [hΔT]; ring
  haveI : IsProbabilityMeasure (lawG1 Δ) := twoPoint_prob _ (by linarith) (by linarith)
  haveI : IsProbabilityMeasure (lawG2 Δ) := twoPoint_prob _ (by linarith) (by linarith)
  rcases le_total (expectedRegret π (lawG2 Δ)) (expectedRegret π (lawG1 Δ)) with h | h
  · exact ⟨lawG1 Δ, inferInstance, supp_two _, by linarith⟩
  · exact ⟨lawG2 Δ, inferInstance, supp_two _, by linarith⟩

end
