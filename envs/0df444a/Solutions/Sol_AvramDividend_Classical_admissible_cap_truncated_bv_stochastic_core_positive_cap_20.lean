-- Prove2me | solution 20 for AvramDividend.Classical.admissible_cap_truncated_bv_stochastic_core_positive_cap
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T07:56:55.61746+00:00
-- url     : https://prove2.me/submissions/6487e2bb-b80f-4851-a1cf-0e3505fbb1ee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramA06Carbon

open Filter Topology ProbabilityTheory

noncomputable section

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-! ### Section 1: Properties of a BV spectrally negative Lévy process -/

private lemma X_measurable (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) :
    Measurable (X.X t) :=
  (X.adapted t).mono (𝓕.le t) le_rfl

private lemma integrableOn_const_of_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : μ s < ⊤) (c : ℝ) : IntegrableOn (fun _ => c) s μ := by
  have : IsFiniteMeasure (μ.restrict s) := ⟨by rw [Measure.restrict_apply_univ]; exact hs⟩
  exact integrable_const c

private lemma drift_pos (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) : 0 < X.drift := by
  by_contra h
  push Not at h
  exact hX.1 ⟨hBV, Or.inl h⟩

private lemma nu_ac_volume (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) : X.ν ≪ volume := by
  rcases hX.2.2 with hσ | hinf | hac
  · linarith [hBV.1]
  · exact absurd hinf (ne_of_lt hBV.2)
  · exact hac

private lemma nu_Iic_neg_lt_top (X : SpectrallyNegativeLevy P 𝓕) {a : ℝ} (ha : 0 < a) :
    X.ν (Iic (-a)) < ⊤ := by
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (min 1 (a ^ 2)) := by
    rw [ENNReal.ofReal_pos]
    exact lt_min zero_lt_one (sq_pos_of_pos ha)
  have hle : ENNReal.ofReal (min 1 (a ^ 2)) * X.ν (Iic (-a)) ≤
      ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν := by
    calc ENNReal.ofReal (min 1 (a ^ 2)) * X.ν (Iic (-a))
        = ∫⁻ _ in Iic (-a), ENNReal.ofReal (min 1 (a ^ 2)) ∂X.ν := by
            rw [setLIntegral_const]
      _ ≤ ∫⁻ y in Iic (-a), ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν := by
            apply setLIntegral_mono' measurableSet_Iic
            intro y hy
            apply ENNReal.ofReal_le_ofReal
            apply min_le_min_left
            have h1 : a ≤ -y := by linarith [Set.mem_Iic.mp hy]
            nlinarith
      _ ≤ ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν := setLIntegral_le_lintegral _ _
  have hfin : ENNReal.ofReal (min 1 (a ^ 2)) * X.ν (Iic (-a)) < ⊤ :=
    lt_of_le_of_lt hle X.ν_integrable
  rcases ENNReal.mul_lt_top_iff.mp hfin with ⟨_, h⟩ | h | h
  · exact h
  · exact absurd h (ne_of_gt hpos)
  · simp [h]

private lemma nu_sigmaFinite (X : SpectrallyNegativeLevy P 𝓕) : SigmaFinite X.ν := by
  refine ⟨⟨⟨fun n => if n = 0 then Ici (0 : ℝ) else Iic (-(1 / (n : ℝ))), fun _ => trivial, ?_, ?_⟩⟩⟩
  · intro n
    split_ifs with hn
    · simp [X.ν_Ici]
    · have hn_pos : (0 : ℝ) < 1 / (n : ℝ) := by
        have : 0 < n := Nat.pos_of_ne_zero hn
        positivity
      exact nu_Iic_neg_lt_top X hn_pos
  · ext y
    simp only [mem_iUnion, mem_univ, iff_true]
    by_cases hy : 0 ≤ y
    · exact ⟨0, by simp [hy]⟩
    · push Not at hy
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt (neg_pos.mpr hy)
      refine ⟨N + 1, ?_⟩
      simp only [Nat.succ_ne_zero, ↓reduceIte, mem_Iic, Nat.cast_add, Nat.cast_one]
      linarith

private lemma nu_Ioo_abs_integrable (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    IntegrableOn (fun y : ℝ => |y|) (Ioo (-1 : ℝ) 0) X.ν := by
  refine ⟨continuous_abs.aestronglyMeasurable, ?_⟩
  have heq : (∫⁻ y in Ioo (-1 : ℝ) 0, ‖|y|‖ₑ ∂X.ν) =
      ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro y _
    simp [Real.enorm_eq_ofReal_abs, abs_abs]
  rw [HasFiniteIntegral, heq]
  exact hBV.2

private lemma nu_Ioo_id_integrable (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    IntegrableOn (fun y : ℝ => y) (Ioo (-1 : ℝ) 0) X.ν := by
  refine (nu_Ioo_abs_integrable X hBV).mono' continuous_id.aestronglyMeasurable ?_
  filter_upwards with y
  simp [Real.norm_eq_abs]

private lemma nu_Iio_exp_sub_one_integrable (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) {θ : ℝ} (hθ : 0 ≤ θ) :
    IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1) (Iio (0 : ℝ)) X.ν := by
  have hsplit : Iio (0 : ℝ) = Iic (-1 : ℝ) ∪ Ioo (-1 : ℝ) 0 := by
    ext y; simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]; constructor
    · intro hy; by_cases h : y ≤ -1
      · exact Or.inl h
      · exact Or.inr ⟨by linarith, hy⟩
    · rintro (h | ⟨_, h⟩) <;> linarith
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hfin : X.ν (Iic (-1 : ℝ)) < ⊤ := by
      simpa using nu_Iic_neg_lt_top X zero_lt_one
    have : IsFiniteMeasure (X.ν.restrict (Iic (-1 : ℝ))) := ⟨by
      rw [Measure.restrict_apply_univ]; exact hfin⟩
    refine (integrable_const (1 : ℝ)).mono'
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub continuous_const).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
    have hy0 : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ (by linarith [mem_Iic.mp hy])
    have hexp1 : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr hy0
    have hexp0 : 0 ≤ Real.exp (θ * y) := le_of_lt (Real.exp_pos _)
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  · refine ((nu_Ioo_abs_integrable X hBV).const_mul θ).mono'
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub continuous_const).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hy0 : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy.2)
    have hexp1 : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr hy0
    have hlow : 1 + θ * y ≤ Real.exp (θ * y) := by linarith [Real.add_one_le_exp (θ * y)]
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith), abs_of_neg hy.2]
    linarith

private lemma nu_Iio_mul_indicator_eq (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (a : ℝ) :
    IntegrableOn (fun y : ℝ => a * y * (Ioo (-1 : ℝ) 1).indicator 1 y) (Iio (0 : ℝ)) X.ν ∧
      (∫ y in Iio (0 : ℝ), a * y * (Ioo (-1 : ℝ) 1).indicator 1 y ∂X.ν) =
        a * ∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν := by
  have heq : EqOn (fun y : ℝ => a * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      ((Ioo (-1 : ℝ) 0).indicator (fun y => a * y)) (Iio (0 : ℝ)) := by
    intro y hy
    dsimp only
    by_cases h : -1 < y
    · have h1 : y ∈ Ioo (-1 : ℝ) 1 := ⟨h, lt_trans hy zero_lt_one⟩
      have h2 : y ∈ Ioo (-1 : ℝ) 0 := ⟨h, hy⟩
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.one_apply, mul_one]
    · have h1 : y ∉ Ioo (-1 : ℝ) 1 := fun hc => h hc.1
      have h2 : y ∉ Ioo (-1 : ℝ) 0 := fun hc => h hc.1
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, mul_zero]
  constructor
  · rw [integrableOn_congr_fun heq measurableSet_Iio]
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo, IntegrableOn,
        Measure.restrict_restrict measurableSet_Ioo]
    have hsub : Ioo (-1 : ℝ) 0 ∩ Iio 0 = Ioo (-1 : ℝ) 0 :=
      inter_eq_left.mpr (fun y hy => hy.2)
    rw [hsub]
    exact (nu_Ioo_id_integrable X hBV).const_mul a
  · rw [setIntegral_congr_fun measurableSet_Iio heq,
        setIntegral_indicator measurableSet_Ioo]
    have hsub : Iio (0 : ℝ) ∩ Ioo (-1 : ℝ) 0 = Ioo (-1 : ℝ) 0 :=
      inter_eq_right.mpr (fun y hy => hy.2)
    rw [hsub, integral_const_mul]

private lemma psi_eq_bv (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    X.ψ θ = X.drift * θ + ∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ∂X.ν := by
  unfold SpectrallyNegativeLevy.ψ laplaceExponent SpectrallyNegativeLevy.drift
  rw [hBV.1]
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, zero_div, add_zero]
  have hint1 := nu_Iio_exp_sub_one_integrable X hBV hθ
  have ⟨hint2, hind_eq⟩ := nu_Iio_mul_indicator_eq X hBV θ
  rw [integral_sub hint1 hint2, hind_eq]
  ring

private lemma psi_le_drift_mul (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    {θ : ℝ} (hθ : 0 ≤ θ) : X.ψ θ ≤ X.drift * θ := by
  rw [psi_eq_bv X hBV hθ]
  have hnonpos : ∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ∂X.ν ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    have : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy))
    show Real.exp (θ * y) - 1 ≤ 0
    linarith
  linarith

private lemma X_le_drift_mul_ae (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (t : ℝ≥0) : ∀ᵐ ω ∂P, X.X t ω ≤ X.drift * (t : ℝ) := by
  have : IsProbabilityMeasure P := X.isProbability
  have hgt_zero : ∀ n : ℕ, P {ω | X.drift * (t : ℝ) + (1 : ℝ) / (n + 1 : ℝ) ≤ X.X t ω} = 0 := by
    intro n
    set η : ℝ := 1 / (n + 1 : ℝ)
    have hη : 0 < η := by positivity
    apply le_antisymm _ zero_le
    have hbound : ∀ θ : ℝ, 0 < θ →
        P {ω | X.drift * (t : ℝ) + η ≤ X.X t ω} ≤ ENNReal.ofReal (Real.exp (-(θ * η))) := by
      intro θ hθ
      have hlap := X.laplace t θ (le_of_lt hθ)
      have hmarkov : ENNReal.ofReal (Real.exp (θ * (X.drift * (t : ℝ) + η))) *
          P {ω | X.drift * (t : ℝ) + η ≤ X.X t ω} ≤
          ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X.X t ω)) ∂P := by
        calc ENNReal.ofReal (Real.exp (θ * (X.drift * (t : ℝ) + η))) *
              P {ω | X.drift * (t : ℝ) + η ≤ X.X t ω}
            = ∫⁻ _ in {ω | X.drift * (t : ℝ) + η ≤ X.X t ω},
                ENNReal.ofReal (Real.exp (θ * (X.drift * (t : ℝ) + η))) ∂P := by
                rw [setLIntegral_const]
          _ ≤ ∫⁻ ω in {ω | X.drift * (t : ℝ) + η ≤ X.X t ω},
                ENNReal.ofReal (Real.exp (θ * X.X t ω)) ∂P := by
                apply lintegral_mono_ae
                filter_upwards [ae_restrict_mem
                  (measurableSet_le measurable_const (X_measurable X t))] with ω hω
                apply ENNReal.ofReal_le_ofReal
                exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω (le_of_lt hθ))
          _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X.X t ω)) ∂P := setLIntegral_le_lintegral _ _
      have hint_eq : ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X.X t ω)) ∂P =
          ENNReal.ofReal (Real.exp ((t : ℝ) * X.ψ θ)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hlap.1
          (ae_of_all P (fun ω => le_of_lt (Real.exp_pos _)))]
        rw [hlap.2]; rfl
      rw [hint_eq] at hmarkov
      have hpsi : (t : ℝ) * X.ψ θ ≤ (t : ℝ) * (X.drift * θ) :=
        mul_le_mul_of_nonneg_left (psi_le_drift_mul X hBV (le_of_lt hθ)) t.coe_nonneg
      have hle2 : ENNReal.ofReal (Real.exp (θ * (X.drift * (t : ℝ) + η))) *
          P {ω | X.drift * (t : ℝ) + η ≤ X.X t ω} ≤
          ENNReal.ofReal (Real.exp (θ * (X.drift * (t : ℝ)))) := by
        refine hmarkov.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
        linarith
      have hpos : ENNReal.ofReal (Real.exp (θ * (X.drift * (t : ℝ) + η))) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
      have htop : ENNReal.ofReal (Real.exp (θ * (X.drift * (t : ℝ) + η))) ≠ ⊤ :=
        ENNReal.ofReal_ne_top
      calc P {ω | X.drift * (t : ℝ) + η ≤ X.X t ω}
          ≤ ENNReal.ofReal (Real.exp (θ * (X.drift * (t : ℝ)))) /
              ENNReal.ofReal (Real.exp (θ * (X.drift * (t : ℝ) + η))) := by
              rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl htop), mul_comm]
              exact hle2
        _ = ENNReal.ofReal (Real.exp (-(θ * η))) := by
              rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
              congr 2; ring
    have htend : Tendsto (fun k : ℕ => ENNReal.ofReal (Real.exp (-((k + 1 : ℝ) * η))))
        atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      refine Real.tendsto_exp_atBot.comp ?_
      have : Tendsto (fun k : ℕ => ((k + 1 : ℝ) * η)) atTop atTop :=
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const hη
      exact tendsto_neg_atTop_atBot.comp this
    exact ge_of_tendsto htend (Eventually.of_forall (fun k => hbound (k + 1) (by positivity)))
  have hunion : P (⋃ n : ℕ, {ω | X.drift * (t : ℝ) + 1 / (n + 1 : ℝ) ≤ X.X t ω}) = 0 :=
    measure_iUnion_null hgt_zero
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hunion
  have hlt : X.drift * (t : ℝ) < X.X t ω := not_le.mp hω
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
  exact mem_iUnion.mpr ⟨n, show X.drift * (t : ℝ) + 1 / ((n : ℝ) + 1) ≤ X.X t ω by linarith⟩

private lemma X_sub_le_drift_mul_ae (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∀ᵐ ω ∂P, X.X t ω - X.X s ω ≤ X.drift * ((t : ℝ) - (s : ℝ)) := by
  have : IsProbabilityMeasure P := X.isProbability
  have hid := X.stationaryIncrements s t hst
  have hae := X_le_drift_mul_ae X hBV (t - s)
  have hmeas : MeasurableSet (Iic (X.drift * ((t : ℝ) - (s : ℝ)))) := measurableSet_Iic
  have h1 : P ((fun ω => X.X t ω - X.X s ω) ⁻¹' Iic (X.drift * ((t : ℝ) - (s : ℝ)))) =
      P (X.X (t - s) ⁻¹' Iic (X.drift * ((t : ℝ) - (s : ℝ)))) :=
    hid.measure_mem_eq hmeas
  have h2 : P (X.X (t - s) ⁻¹' Iic (X.drift * ((t : ℝ) - (s : ℝ)))) = 1 := by
    have hcoe : ((t - s : ℝ≥0) : ℝ) = (t : ℝ) - (s : ℝ) := NNReal.coe_sub hst
    rw [← hcoe]
    have hc : P (X.X (t - s) ⁻¹' Iic (X.drift * ((t - s : ℝ≥0) : ℝ)))ᶜ = 0 := by
      rwa [ae_iff] at hae
    have hm : MeasurableSet (X.X (t - s) ⁻¹' Iic (X.drift * ((t - s : ℝ≥0) : ℝ))) :=
      measurableSet_Iic.preimage (X_measurable X (t - s))
    have := measure_add_measure_compl hm (μ := P)
    rw [hc, add_zero, measure_univ] at this
    exact this
  rw [h2] at h1
  have hm : MeasurableSet ((fun ω => X.X t ω - X.X s ω) ⁻¹' Iic (X.drift * ((t : ℝ) - (s : ℝ)))) :=
    measurableSet_Iic.preimage ((X_measurable X t).sub (X_measurable X s))
  rw [ae_iff]
  have hcompl : P ((fun ω => X.X t ω - X.X s ω) ⁻¹' Iic (X.drift * ((t : ℝ) - (s : ℝ))))ᶜ = 0 := by
    have hsum := measure_add_measure_compl hm (μ := P)
    rw [h1, measure_univ] at hsum
    exact (ENNReal.add_right_inj ENNReal.one_ne_top).mp (by simpa using hsum)
  convert hcompl using 2
  ext ω; simp [not_le]

private def PathBV (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) : Prop :=
  ∀ s t : ℝ≥0, s ≤ t → X.X t ω - X.X s ω ≤ X.drift * ((t : ℝ) - (s : ℝ))

private lemma pathBV_ae (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, PathBV X ω := by
  have hrat : ∀ p : ℚ × ℚ, ∀ᵐ ω ∂P,
      (p.1 : ℝ).toNNReal ≤ (p.2 : ℝ).toNNReal →
        X.X (p.2 : ℝ).toNNReal ω - X.X (p.1 : ℝ).toNNReal ω ≤
          X.drift * (((p.2 : ℝ).toNNReal : ℝ) - ((p.1 : ℝ).toNNReal : ℝ)) := by
    intro p
    by_cases hp : (p.1 : ℝ).toNNReal ≤ (p.2 : ℝ).toNNReal
    · filter_upwards [X_sub_le_drift_mul_ae X hBV hp] with ω hω _
      exact hω
    · exact ae_of_all P (fun _ h => absurd h hp)
  filter_upwards [ae_all_iff.mpr hrat] with ω hω s t hst
  rcases eq_or_lt_of_le hst with rfl | hlt
  · simp
  · have hltR : (s : ℝ) < (t : ℝ) := hlt
    have hseq : ∀ n : ℕ, ∃ q1 q2 : ℚ,
        (s : ℝ) < q1 ∧ (q1 : ℝ) < min (t : ℝ) ((s : ℝ) + 1 / (n + 1 : ℝ)) ∧
        (t : ℝ) < q2 ∧ (q2 : ℝ) < (t : ℝ) + 1 / (n + 1 : ℝ) := by
      intro n
      have h1 : (s : ℝ) < min (t : ℝ) ((s : ℝ) + 1 / (n + 1 : ℝ)) :=
        lt_min hltR (by linarith [show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity])
      obtain ⟨q1, hq1a, hq1b⟩ := exists_rat_btwn h1
      obtain ⟨q2, hq2a, hq2b⟩ := exists_rat_btwn
        (show (t : ℝ) < (t : ℝ) + 1 / (n + 1 : ℝ) by linarith [show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity])
      exact ⟨q1, q2, hq1a, hq1b, hq2a, hq2b⟩
    choose q1 q2 hq using hseq
    have ht_zero : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hq1_tend : Tendsto (fun n => (q1 n : ℝ).toNNReal) atTop (𝓝 s) := by
      rw [← NNReal.tendsto_coe]
      have hhi : Tendsto (fun n : ℕ => (s : ℝ) + 1 / (n + 1 : ℝ)) atTop (𝓝 (s : ℝ)) := by
        simpa [add_zero] using (tendsto_const_nhds (x := (s : ℝ))).add ht_zero
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhi ?_ ?_
      · intro n; dsimp only
        have hq1_nn : 0 ≤ (q1 n : ℝ) := le_trans s.coe_nonneg (le_of_lt (hq n).1)
        rw [Real.coe_toNNReal _ hq1_nn]
        exact le_of_lt (hq n).1
      · intro n; dsimp only
        have hq1_nn : 0 ≤ (q1 n : ℝ) := le_trans s.coe_nonneg (le_of_lt (hq n).1)
        rw [Real.coe_toNNReal _ hq1_nn]
        exact le_of_lt (lt_of_lt_of_le (hq n).2.1 (min_le_right _ _))
    have hq2_tend : Tendsto (fun n => (q2 n : ℝ).toNNReal) atTop (𝓝 t) := by
      rw [← NNReal.tendsto_coe]
      have hhi : Tendsto (fun n : ℕ => (t : ℝ) + 1 / (n + 1 : ℝ)) atTop (𝓝 (t : ℝ)) := by
        simpa [add_zero] using (tendsto_const_nhds (x := (t : ℝ))).add ht_zero
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhi ?_ ?_
      · intro n; dsimp only
        have hq2_nn : 0 ≤ (q2 n : ℝ) := le_trans t.coe_nonneg (le_of_lt (hq n).2.2.1)
        rw [Real.coe_toNNReal _ hq2_nn]
        exact le_of_lt (hq n).2.2.1
      · intro n; dsimp only
        have hq2_nn : 0 ≤ (q2 n : ℝ) := le_trans t.coe_nonneg (le_of_lt (hq n).2.2.1)
        rw [Real.coe_toNNReal _ hq2_nn]
        exact le_of_lt (hq n).2.2.2
    have hq1_nhds : Tendsto (fun n => (q1 n : ℝ).toNNReal) atTop (𝓝[≥] s) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hq1_tend
        (Eventually.of_forall fun n => by
          rw [mem_Ici, ← NNReal.coe_le_coe, Real.coe_toNNReal _ (le_trans s.coe_nonneg (le_of_lt (hq n).1))]
          exact le_of_lt (hq n).1)
    have hq2_nhds : Tendsto (fun n => (q2 n : ℝ).toNNReal) atTop (𝓝[≥] t) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hq2_tend
        (Eventually.of_forall fun n => by
          rw [mem_Ici, ← NNReal.coe_le_coe, Real.coe_toNNReal _ (le_trans t.coe_nonneg (le_of_lt (hq n).2.2.1))]
          exact le_of_lt (hq n).2.2.1)
    have hX1 : Tendsto (fun n => X.X (q1 n : ℝ).toNNReal ω) atTop (𝓝 (X.X s ω)) :=
      (X.rightCont ω s).tendsto.comp hq1_nhds
    have hX2 : Tendsto (fun n => X.X (q2 n : ℝ).toNNReal ω) atTop (𝓝 (X.X t ω)) :=
      (X.rightCont ω t).tendsto.comp hq2_nhds
    have hRHS : Tendsto (fun n => X.drift * (((q2 n : ℝ).toNNReal : ℝ) - ((q1 n : ℝ).toNNReal : ℝ)))
        atTop (𝓝 (X.drift * ((t : ℝ) - (s : ℝ)))) :=
      tendsto_const_nhds.mul ((NNReal.tendsto_coe.mpr hq2_tend).sub (NNReal.tendsto_coe.mpr hq1_tend))
    refine le_of_tendsto_of_tendsto (hX2.sub hX1) hRHS (Eventually.of_forall fun n => ?_)
    apply hω (q1 n, q2 n)
    rw [← NNReal.coe_le_coe,
        Real.coe_toNNReal _ (le_trans s.coe_nonneg (le_of_lt (hq n).1)),
        Real.coe_toNNReal _ (le_trans t.coe_nonneg (le_of_lt (hq n).2.2.1))]
    exact le_of_lt (lt_trans (lt_of_lt_of_le (hq n).2.1 (min_le_left _ _)) (hq n).2.2.1)

private lemma S_integrable (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (t : ℝ≥0) :
    Integrable (fun ω => X.drift * (t : ℝ) - X.X t ω) P := by
  have : IsProbabilityMeasure P := X.isProbability
  have hS1_int : Integrable (fun ω => X.drift - X.X 1 ω) P :=
    (integrable_const X.drift).sub hX.2.1
  have hS_nat : ∀ n : ℕ, Integrable (fun ω => X.drift * (n : ℝ) - X.X (n : ℝ≥0) ω) P := by
    intro n
    induction n with
    | zero =>
      have h0 : (fun ω => X.drift * ((0 : ℕ) : ℝ) - X.X ((0 : ℕ) : ℝ≥0) ω) = 0 := by
        ext ω; simp [X.X_zero ω]
      rw [h0]; exact integrable_zero _ _ _
    | succ n ih =>
      have hstep_id : IdentDistrib (fun ω => X.drift - (X.X ((n + 1 : ℕ) : ℝ≥0) ω - X.X (n : ℝ≥0) ω))
          (fun ω => X.drift - X.X 1 ω) P P := by
        have h1 := X.stationaryIncrements (n : ℝ≥0) ((n + 1 : ℕ) : ℝ≥0) (by exact_mod_cast Nat.le_succ n)
        have hsub : ((n + 1 : ℕ) : ℝ≥0) - (n : ℝ≥0) = 1 := by ext; simp
        rw [hsub] at h1
        exact h1.comp (measurable_const.sub measurable_id)
      have hstep_int := hstep_id.integrable_iff.mpr hS1_int
      have hdecomp : (fun ω => X.drift * ((n + 1 : ℕ) : ℝ) - X.X ((n + 1 : ℕ) : ℝ≥0) ω) =
          (fun ω => (X.drift * (n : ℝ) - X.X (n : ℝ≥0) ω) +
            (X.drift - (X.X ((n + 1 : ℕ) : ℝ≥0) ω - X.X (n : ℝ≥0) ω))) := by
        ext ω; push_cast; ring
      rw [hdecomp]; exact ih.add hstep_int
  obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
  have hle : t ≤ (n : ℝ≥0) := by exact_mod_cast hn
  refine (hS_nat n).mono'
    (aestronglyMeasurable_const.sub (X_measurable X t).aestronglyMeasurable) ?_
  filter_upwards [X_le_drift_mul_ae X hBV t, X_sub_le_drift_mul_ae X hBV hle] with ω h1 h2
  rw [NNReal.coe_natCast] at h2
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

/-! ### Section 2: Extension `wExt` and generator bounds -/

private lemma w_sub_ge_sub {w : ℝ → ℝ} {C : ℝ≥0∞}
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbC : ENNReal.ofReal b ≤ C) :
    b - a ≤ w b - w a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  · have hsub : Ioo a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
      intro y hy
      refine ⟨lt_of_le_of_lt ha hy.1, ?_⟩
      calc ENNReal.ofReal y < ENNReal.ofReal b :=
            (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ha hlt)).mpr hy.2
        _ ≤ C := hbC
    have hcont : ContinuousOn w (Icc a b) :=
      hw_cont.mono (fun y hy => le_trans ha hy.1)
    have hdiff : DifferentiableOn ℝ w (Ioo a b) :=
      (hw_smooth.differentiableOn one_ne_zero).mono hsub
    obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_slope w hlt hcont hdiff
    have hc1 : 1 ≤ deriv w c := hw_grad c (hsub hc).1 (hsub hc).2
    rw [hderiv, le_div_iff₀ (sub_pos.mpr hlt)] at hc1
    linarith

private def wExt (w : ℝ → ℝ) (C : ℝ≥0∞) (z : ℝ) : ℝ :=
  if C = ⊤ then w z else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)

private lemma wExt_eq_of_le {w : ℝ → ℝ} {C : ℝ≥0∞} {z : ℝ} (hz : ENNReal.ofReal z ≤ C) :
    wExt w C z = w z := by
  unfold wExt
  split_ifs with htop hle
  · rfl
  · rfl
  · exfalso
    exact hle ((ENNReal.ofReal_le_iff_le_toReal htop).mp hz)

private lemma wExt_eq_zero_of_neg {w : ℝ → ℝ} {C : ℝ≥0∞} (hw_neg : ∀ y < 0, w y = 0)
    {z : ℝ} (hz : z < 0) : wExt w C z = 0 := by
  rw [wExt_eq_of_le (by rw [ENNReal.ofReal_of_nonpos (le_of_lt hz)]; exact zero_le)]
  exact hw_neg z hz

private lemma wExt_continuousOn {w : ℝ → ℝ} {C : ℝ≥0∞} (hw_cont : ContinuousOn w (Ici 0)) :
    ContinuousOn (wExt w C) (Ici 0) := by
  unfold wExt
  split_ifs with htop
  · exact hw_cont
  · intro z hz
    by_cases hlt : z < C.toReal
    · apply ContinuousWithinAt.congr_of_eventuallyEq (hw_cont z hz)
      · filter_upwards [nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hlt)] with y hy
        simp [le_of_lt (mem_Iio.mp hy)]
      · simp [le_of_lt hlt]
    · by_cases hgt : C.toReal < z
      · have hcont2 : ContinuousWithinAt (fun y => w C.toReal + (y - C.toReal)) (Ici 0) z :=
          (continuous_const.add (continuous_id.sub continuous_const)).continuousWithinAt
        apply hcont2.congr_of_eventuallyEq
        · filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hgt)] with y hy
          simp [not_le.mpr (mem_Ioi.mp hy)]
        · simp [not_le.mpr hgt]
      · have heq : z = C.toReal := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
        rw [heq]
        have hleft : ContinuousWithinAt (fun y => if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal)) (Iic C.toReal ∩ Ici 0) C.toReal := by
          apply (hw_cont C.toReal (heq ▸ hz)).mono inter_subset_right |>.congr_of_eventuallyEq
          · filter_upwards [self_mem_nhdsWithin] with y hy
            exact if_pos (mem_Iic.mp hy.1)
          · simp
        have hright : ContinuousWithinAt (fun y => if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal)) (Ici C.toReal ∩ Ici 0) C.toReal := by
          have hc : ContinuousWithinAt (fun y => w C.toReal + (y - C.toReal)) (Ici C.toReal ∩ Ici 0) C.toReal :=
            (continuous_const.add (continuous_id.sub continuous_const)).continuousWithinAt
          apply hc.congr_of_eventuallyEq
          · filter_upwards [self_mem_nhdsWithin] with y hy
            by_cases h : y ≤ C.toReal
            · have : y = C.toReal := le_antisymm h hy.1
              subst this; simp
            · simp [h]
          · simp
        have hunion : (Iic C.toReal ∩ Ici 0) ∪ (Ici C.toReal ∩ Ici 0) = Ici 0 := by
          ext y; simp only [mem_union, mem_inter_iff, mem_Iic, mem_Ici]
          constructor
          · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
          · intro h; rcases le_total y C.toReal with h1 | h1
            · exact Or.inl ⟨h1, h⟩
            · exact Or.inr ⟨h1, h⟩
        rw [← hunion]
        exact hleft.union hright

private lemma wExt_sub_ge_sub {w : ℝ → ℝ} {C : ℝ≥0∞}
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    b - a ≤ wExt w C b - wExt w C a := by
  by_cases htop : C = ⊤
  · simp only [wExt, htop, ↓reduceIte]
    exact w_sub_ge_sub hw_cont hw_smooth hw_grad ha hab (by rw [htop]; exact le_top)
  · by_cases hb : b ≤ C.toReal
    · rw [wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr hb),
          wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr (le_trans hab hb))]
      exact w_sub_ge_sub hw_cont hw_smooth hw_grad ha hab ((ENNReal.ofReal_le_iff_le_toReal htop).mpr hb)
    · by_cases ha' : a ≤ C.toReal
      · have h1 : C.toReal - a ≤ w C.toReal - w a :=
          w_sub_ge_sub hw_cont hw_smooth hw_grad ha ha' ((ENNReal.ofReal_le_iff_le_toReal htop).mpr le_rfl)
        rw [wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr ha')]
        simp only [wExt, htop, ↓reduceIte, hb]
        linarith
      · simp only [wExt, htop, ↓reduceIte, hb, ha']
        linarith

private lemma wExt_nonneg {w : ℝ → ℝ} {C : ℝ≥0∞}
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (z : ℝ) : 0 ≤ wExt w C z := by
  by_cases hz : z < 0
  · rw [wExt_eq_zero_of_neg hw_neg hz]
  · push Not at hz
    have h1 := wExt_sub_ge_sub hw_cont hw_smooth hw_grad le_rfl hz
    have h0 : wExt w C 0 = w 0 := wExt_eq_of_le (by simp)
    linarith

private lemma wExt_mono {w : ℝ → ℝ} {C : ℝ≥0∞}
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    Monotone (wExt w C) := by
  intro a b hab
  by_cases ha : a < 0
  · rw [wExt_eq_zero_of_neg hw_neg ha]
    exact wExt_nonneg hw_cont hw0 hw_neg hw_smooth hw_grad b
  · push Not at ha
    have := wExt_sub_ge_sub hw_cont hw_smooth hw_grad ha hab
    linarith

private lemma generator_eq_bv (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    {f : ℝ → ℝ} {y : ℝ}
    (hint : X.GeneratorIntegrable f y) :
    IntegrableOn (fun u : ℝ => f (y + u) - f y) (Iio (0 : ℝ)) X.ν ∧
      X.generator f y = X.drift * deriv f y + ∫ u in Iio (0 : ℝ), (f (y + u) - f y) ∂X.ν := by
  have ⟨hint2, hind_eq⟩ := nu_Iio_mul_indicator_eq X hBV (deriv f y)
  have hsum : (fun u : ℝ => f (y + u) - f y) =
      (fun u : ℝ => SpectrallyNegativeLevy.generatorIntegrand f y u +
        deriv f y * u * (Ioo (-1 : ℝ) 1).indicator 1 u) := by
    ext u; unfold SpectrallyNegativeLevy.generatorIntegrand; ring
  have hint1 : IntegrableOn (fun u : ℝ => f (y + u) - f y) (Iio (0 : ℝ)) X.ν := by
    rw [hsum]; exact hint.add hint2
  refine ⟨hint1, ?_⟩
  unfold SpectrallyNegativeLevy.generator SpectrallyNegativeLevy.drift
  rw [hBV.1]
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, zero_mul, zero_add]
  have hgen_sub : (∫ u in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand f y u ∂X.ν) =
      (∫ u in Iio (0 : ℝ), (f (y + u) - f y) ∂X.ν) -
      (∫ u in Iio (0 : ℝ), deriv f y * u * (Ioo (-1 : ℝ) 1).indicator 1 u ∂X.ν) := by
    unfold SpectrallyNegativeLevy.generatorIntegrand
    exact integral_sub hint1 hint2
  rw [hgen_sub, hind_eq]
  ring

private lemma exists_small_nu_tail (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∫ u in Ioo (-a) 0, |u| ∂X.ν ≤ ε := by
  have htend : Tendsto (fun n : ℕ => ∫ u in Ioo (-((1 : ℝ) / (n + 2 : ℝ))) 0, |u| ∂X.ν)
      atTop (𝓝 0) := by
    have hrew : ∀ n : ℕ, (∫ u in Ioo (-((1 : ℝ) / (n + 2 : ℝ))) 0, |u| ∂X.ν) =
        ∫ u in Ioo (-1 : ℝ) 0, (Ioo (-((1 : ℝ) / (n + 2 : ℝ))) 0).indicator (fun u => |u|) u ∂X.ν := by
      intro n
      rw [setIntegral_indicator measurableSet_Ioo]
      have hsub : Ioo (-1 : ℝ) 0 ∩ Ioo (-((1 : ℝ) / (n + 2 : ℝ))) 0 =
          Ioo (-((1 : ℝ) / (n + 2 : ℝ))) 0 := by
        apply inter_eq_right.mpr
        intro u hu
        refine ⟨lt_trans ?_ hu.1, hu.2⟩
        have : (1 : ℝ) / (n + 2 : ℝ) < 1 := by
          rw [div_lt_one (by positivity)]; linarith
        linarith
      rw [hsub]
    simp_rw [hrew]
    have htend0 : Tendsto (fun n : ℕ => ∫ u in Ioo (-1 : ℝ) 0,
        (Ioo (-((1 : ℝ) / (n + 2 : ℝ))) 0).indicator (fun u => |u|) u ∂X.ν)
        atTop (𝓝 (∫ _ in Ioo (-1 : ℝ) 0, (0 : ℝ) ∂X.ν)) := by
      apply tendsto_integral_of_dominated_convergence (fun u : ℝ => |u|)
      · intro n
        exact (continuous_abs.aestronglyMeasurable).indicator measurableSet_Ioo
      · exact nu_Ioo_abs_integrable X hBV
      · intro n
        filter_upwards with u
        by_cases h : u ∈ Ioo (-((1 : ℝ) / (n + 2 : ℝ))) 0
        · rw [Set.indicator_of_mem h, Real.norm_eq_abs, abs_abs]
        · rw [Set.indicator_of_notMem h, norm_zero]; exact abs_nonneg u
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        have hneg : 0 < -u := neg_pos.mpr hu.2
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hneg
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        have h1 : (1 : ℝ) / (n + 2 : ℝ) < -u := by
          have hle : (1 : ℝ) / (n + 2 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
            apply one_div_le_one_div_of_le (by positivity)
            have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            linarith
          exact lt_of_le_of_lt hle hN
        have hnot : u ∉ Ioo (-((1 : ℝ) / (n + 2 : ℝ))) 0 := fun hc => by linarith [hc.1]
        exact (Set.indicator_of_notMem hnot _).symm
    simpa using htend0
  obtain ⟨n, hn⟩ := (tendsto_order.mp htend).2 ε hε |>.exists
  refine ⟨1 / (n + 2 : ℝ), by positivity, ?_, le_of_lt hn⟩
  rw [div_lt_one (by positivity)]; linarith

private lemma deriv_w_bdd_near_C (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) {q : ℝ} (hq : 0 < q)
    {w : ℝ → ℝ} {C : ℝ≥0∞} (hC : 0 < C) (hCtop : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ y : ℝ, C.toReal / 2 ≤ y → y < C.toReal → deriv w y ≤ L := by
  set c₀ := C.toReal
  have hc₀ : 0 < c₀ := ENNReal.toReal_pos (ne_of_gt hC) hCtop
  have hd : 0 < X.drift := drift_pos X hX hBV
  obtain ⟨a₀, ha₀_pos, ha₀_lt1, ha₀_int⟩ := exists_small_nu_tail X hBV (half_pos hd)
  set a := min a₀ (c₀ / 4)
  have ha_pos : 0 < a := lt_min ha₀_pos (by linarith)
  have ha_lt : a ≤ c₀ / 4 := min_le_right _ _
  have ha_int : ∫ u in Ioo (-a) 0, |u| ∂X.ν ≤ X.drift / 2 := by
    refine le_trans ?_ ha₀_int
    apply setIntegral_mono_set
    · exact (nu_Ioo_abs_integrable X hBV).mono_set
        (fun u hu => ⟨by linarith [hu.1, ha₀_lt1], hu.2⟩)
    · exact ae_of_all _ (fun u => abs_nonneg u)
    · exact Eventually.of_forall (fun u hu => ⟨by linarith [hu.1, min_le_left a₀ (c₀ / 4)], hu.2⟩)
  have hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    isOpen_Ioi.inter (isOpen_lt ENNReal.continuous_ofReal continuous_const)
  have hderiv_cont : ContinuousOn (deriv w) {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.continuousOn_deriv_of_isOpen hopen le_rfl
  have hsub_compact : Icc (c₀ / 2) (c₀ / 2 + a) ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    refine ⟨by linarith [hy.1], (ENNReal.ofReal_lt_iff_lt_toReal (by linarith [hy.1]) hCtop).mpr (by linarith [hy.2])⟩
  obtain ⟨K0, hK0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hderiv_cont.mono hsub_compact)
  have hK0' : ∀ y ∈ Icc (c₀ / 2) (c₀ / 2 + a), deriv w y ≤ K0 :=
    fun y hy => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hK0 y hy)
  have hnu_tail : X.ν (Iic (-a)) < ⊤ := nu_Iic_neg_lt_top X ha_pos
  have hwc₀ : 0 ≤ w c₀ := by
    have := wExt_nonneg hw_cont hw0 hw_neg hw_smooth hw_grad c₀
    rwa [wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal hCtop).mpr le_rfl)] at this
  set K1 := (2 / X.drift) * (q * w c₀ + w c₀ * (X.ν (Iic (-a))).toReal)
  refine ⟨max 1 (max K0 K1), le_max_left _ _, ?_⟩
  intro y hy1 hy2
  set b := max y (c₀ / 2 + a)
  have hb_lt : b < c₀ := max_lt hy2 (by linarith)
  have hsub_b : Icc (c₀ / 2) b ⊆ {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} := by
    intro z hz
    refine ⟨by linarith [hz.1], (ENNReal.ofReal_lt_iff_lt_toReal (by linarith [hz.1]) hCtop).mpr (lt_of_le_of_lt hz.2 hb_lt)⟩
  have hne : (Icc (c₀ / 2) b).Nonempty := ⟨c₀ / 2, le_rfl, by linarith [le_max_right y (c₀ / 2 + a)]⟩
  obtain ⟨yStar, hyStar_mem, hyStar_max⟩ :=
    isCompact_Icc.exists_isMaxOn hne (hderiv_cont.mono hsub_b)
  have hy_le : deriv w y ≤ deriv w yStar := hyStar_max ⟨hy1, le_max_left _ _⟩
  refine le_trans hy_le ?_
  by_cases hcase : yStar ≤ c₀ / 2 + a
  · exact le_trans (hK0' yStar ⟨hyStar_mem.1, hcase⟩) (le_trans (le_max_left _ _) (le_max_right _ _))
  · push Not at hcase
    have hgen := hw_gen yStar (hsub_b hyStar_mem).1 (hsub_b hyStar_mem).2
    have ⟨hint_diff, hgen_eq⟩ := generator_eq_bv X hBV hgen.1
    have hgen_le : X.drift * deriv w yStar + ∫ u in Iio (0 : ℝ), (w (yStar + u) - w yStar) ∂X.ν ≤ q * w yStar := by
      linarith [hgen.2]
    have hsplit : Iio (0 : ℝ) = Iic (-a) ∪ Ioo (-a) 0 := by
      ext u; simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]; constructor
      · intro hu; by_cases h : u ≤ -a
        · exact Or.inl h
        · exact Or.inr ⟨by linarith, hu⟩
      · rintro (h | ⟨_, h⟩) <;> linarith
    have hdisj : Disjoint (Iic (-a)) (Ioo (-a) 0) := by
      rw [Set.disjoint_left]; intro u h1 h2; linarith [mem_Iic.mp h1, h2.1]
    have hint_neg : IntegrableOn (fun u => w yStar - w (yStar + u)) (Iio (0 : ℝ)) X.ν := by
      have : (fun u => w yStar - w (yStar + u)) = fun u => -(w (yStar + u) - w yStar) := by ext u; ring
      rw [this]; exact hint_diff.neg
    have hbound1 : ∫ u in Iic (-a), (w yStar - w (yStar + u)) ∂X.ν ≤ w c₀ * (X.ν (Iic (-a))).toReal := by
      calc ∫ u in Iic (-a), (w yStar - w (yStar + u)) ∂X.ν
          ≤ ∫ _ in Iic (-a), w c₀ ∂X.ν := by
            apply setIntegral_mono_on (hint_neg.mono_set (fun u hu => lt_of_le_of_lt hu (neg_lt_zero.mpr ha_pos)))
              (integrableOn_const_of_lt_top hnu_tail (w c₀)) measurableSet_Iic
            intro u hu
            have hwy : w yStar ≤ w c₀ := by
              have h1 := wExt_mono hw_cont hw0 hw_neg hw_smooth hw_grad (le_of_lt (lt_of_le_of_lt hyStar_mem.2 hb_lt))
              rwa [wExt_eq_of_le (le_of_lt (hsub_b hyStar_mem).2),
                   wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal hCtop).mpr le_rfl)] at h1
            have hw0' : 0 ≤ w (yStar + u) := by
              have h1 := wExt_nonneg hw_cont hw0 hw_neg hw_smooth hw_grad (yStar + u)
              have hle_c : ENNReal.ofReal (yStar + u) ≤ C := by
                by_cases hneg : yStar + u ≤ 0
                · rw [ENNReal.ofReal_of_nonpos hneg]; exact zero_le
                · push Not at hneg
                  exact (ENNReal.ofReal_le_iff_le_toReal hCtop).mpr (by linarith [hyStar_mem.2, hb_lt, mem_Iic.mp hu])
              rwa [wExt_eq_of_le hle_c] at h1
            linarith
        _ = (X.ν (Iic (-a))).toReal * w c₀ := by
            rw [setIntegral_const, smul_eq_mul, Measure.real_def]
        _ = w c₀ * (X.ν (Iic (-a))).toReal := mul_comm _ _
    have hbound2 : ∫ u in Ioo (-a) 0, (w yStar - w (yStar + u)) ∂X.ν ≤
        deriv w yStar * (X.drift / 2) := by
      have hint_abs : IntegrableOn (fun u => |u|) (Ioo (-a) 0) X.ν :=
        (nu_Ioo_abs_integrable X hBV).mono_set (fun u hu => ⟨by linarith [hu.1, min_le_left a₀ (c₀ / 4), ha₀_lt1], hu.2⟩)
      calc ∫ u in Ioo (-a) 0, (w yStar - w (yStar + u)) ∂X.ν
          ≤ ∫ u in Ioo (-a) 0, (deriv w yStar * |u|) ∂X.ν := by
            apply setIntegral_mono_on (hint_neg.mono_set (fun u hu => hu.2))
              (hint_abs.const_mul _) measurableSet_Ioo
            intro u hu
            have h2 : yStar + u < yStar := by linarith [hu.2]
            have hcont_seg : ContinuousOn w (Icc (yStar + u) yStar) :=
              hw_cont.mono (fun z hz => show 0 ≤ z by linarith [hz.1, hu.1])
            have hdiff_seg : DifferentiableOn ℝ w (Ioo (yStar + u) yStar) :=
              (hw_smooth.differentiableOn one_ne_zero).mono
                (fun z hz => hsub_b ⟨by linarith [hz.1, hu.1], le_trans (le_of_lt hz.2) hyStar_mem.2⟩)
            obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope w h2 hcont_seg hdiff_seg
            have hξ_le : deriv w ξ ≤ deriv w yStar :=
              hyStar_max ⟨by linarith [hξ.1, hu.1], le_trans (le_of_lt hξ.2) hyStar_mem.2⟩
            rw [hslope, div_le_iff₀ (sub_pos.mpr h2)] at hξ_le
            have habs : |u| = yStar - (yStar + u) := by rw [abs_of_neg hu.2]; ring
            rw [habs]; linarith
        _ = deriv w yStar * ∫ u in Ioo (-a) 0, |u| ∂X.ν := integral_const_mul _ _
        _ ≤ deriv w yStar * (X.drift / 2) := by
            apply mul_le_mul_of_nonneg_left ha_int
            linarith [hw_grad yStar (hsub_b hyStar_mem).1 (hsub_b hyStar_mem).2]
    have hneg_sum : ∫ u in Iio (0 : ℝ), (w yStar - w (yStar + u)) ∂X.ν =
        (∫ u in Iic (-a), (w yStar - w (yStar + u)) ∂X.ν) +
        (∫ u in Ioo (-a) 0, (w yStar - w (yStar + u)) ∂X.ν) := by
      rw [hsplit, setIntegral_union hdisj measurableSet_Ioo
        (hint_neg.mono_set (fun u hu => lt_of_le_of_lt hu (neg_lt_zero.mpr ha_pos)))
        (hint_neg.mono_set (fun u hu => hu.2))]
    have hflip : ∫ u in Iio (0 : ℝ), (w (yStar + u) - w yStar) ∂X.ν =
        -(∫ u in Iio (0 : ℝ), (w yStar - w (yStar + u)) ∂X.ν) := by
      have : (fun u => w (yStar + u) - w yStar) = fun u => -(w yStar - w (yStar + u)) := by ext u; ring
      rw [this, integral_neg]
    have hwy_le : w yStar ≤ w c₀ := by
      have h1 := wExt_mono hw_cont hw0 hw_neg hw_smooth hw_grad (le_of_lt (lt_of_le_of_lt hyStar_mem.2 hb_lt))
      rwa [wExt_eq_of_le (le_of_lt (hsub_b hyStar_mem).2),
           wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal hCtop).mpr le_rfl)] at h1
    have hfinal : X.drift / 2 * deriv w yStar ≤ q * w c₀ + w c₀ * (X.ν (Iic (-a))).toReal := by
      have hqle : q * w yStar ≤ q * w c₀ := mul_le_mul_of_nonneg_left hwy_le (le_of_lt hq)
      linarith
    have hle_K1 : deriv w yStar ≤ K1 := by
      have : deriv w yStar ≤ (q * w c₀ + w c₀ * (X.ν (Iic (-a))).toReal) / (X.drift / 2) :=
        (le_div_iff₀ (half_pos hd)).mpr (by linarith)
      calc deriv w yStar ≤ (q * w c₀ + w c₀ * (X.ν (Iic (-a))).toReal) / (X.drift / 2) := this
        _ = K1 := by simp only [K1]; field_simp [ne_of_gt hd]
    exact le_trans hle_K1 (le_trans (le_max_right _ _) (le_max_right _ _))

private lemma wExt_lipschitz_above_half_C {w : ℝ → ℝ} {C : ℝ≥0∞} (_hC : 0 < C) (hCtop : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    {L : ℝ} (hL1 : 1 ≤ L) (hL : ∀ y : ℝ, C.toReal / 2 ≤ y → y < C.toReal → deriv w y ≤ L)
    {a b : ℝ} (ha : C.toReal / 2 ≤ a) (hab : a ≤ b) :
    wExt w C b - wExt w C a ≤ L * (b - a) := by
  set c₀ := C.toReal
  have hseg : ∀ {u v : ℝ}, c₀ / 2 ≤ u → u ≤ v → v ≤ c₀ → w v - w u ≤ L * (v - u) := by
    intro u v hu huv hv
    rcases eq_or_lt_of_le huv with rfl | hlt
    · simp
    · have hc₀ : 0 < c₀ := ENNReal.toReal_pos (ne_of_gt _hC) hCtop
      have hcont : ContinuousOn w (Icc u v) :=
        hw_cont.mono (fun z hz => show 0 ≤ z by linarith [hz.1])
      have hdiff : DifferentiableOn ℝ w (Ioo u v) :=
        (hw_smooth.differentiableOn one_ne_zero).mono (fun z hz =>
          ⟨by linarith [hz.1],
           (ENNReal.ofReal_lt_iff_lt_toReal (by linarith [hz.1]) hCtop).mpr (lt_of_lt_of_le hz.2 hv)⟩)
      obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope w hlt hcont hdiff
      have hle : deriv w ξ ≤ L := hL ξ (by linarith [hξ.1]) (lt_of_lt_of_le hξ.2 hv)
      rw [hslope, div_le_iff₀ (sub_pos.mpr hlt)] at hle
      linarith
  by_cases hb : b ≤ c₀
  · rw [wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal hCtop).mpr hb),
        wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal hCtop).mpr (le_trans hab hb))]
    exact hseg ha hab hb
  · by_cases ha' : a ≤ c₀
    · have h1 := hseg ha ha' le_rfl
      rw [wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal hCtop).mpr ha')]
      have hb' : ¬ b ≤ C.toReal := hb
      simp only [wExt, hCtop, ↓reduceIte, hb']
      have h2 : 1 * (b - c₀) ≤ L * (b - c₀) := mul_le_mul_of_nonneg_right hL1 (by linarith)
      linarith
    · have hb' : ¬ b ≤ C.toReal := hb
      have ha'' : ¬ a ≤ C.toReal := ha'
      simp only [wExt, hCtop, ↓reduceIte, hb', ha'']
      have h2 : 1 * (b - a) ≤ L * (b - a) := mul_le_mul_of_nonneg_right hL1 (by linarith)
      linarith

private lemma exists_wExt_gen_error (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) {q : ℝ} (hq : 0 < q)
    {w : ℝ → ℝ} {C : ℝ≥0∞} (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∃ η : ℝ → ℝ, (∀ r, 0 ≤ η r) ∧ Tendsto η (𝓝[>] 0) (𝓝 0) ∧
      ∀ r : ℝ, 0 < r → (C ≠ ⊤ → r < C.toReal / 8) →
      ∀ z : ℝ, 0 < z → (C = ⊤ ∨ z < C.toReal + r) → (C ≠ ⊤ → z ≠ C.toReal) →
        IntegrableOn (fun u => wExt w C (z + u) - wExt w C z) (Iio (0 : ℝ)) X.ν ∧
        X.drift * deriv (wExt w C) z +
          ∫ u in Iio (0 : ℝ), (wExt w C (z + u) - wExt w C z) ∂X.ν -
          q * wExt w C z ≤ η r := by
  by_cases htop : C = ⊤
  · refine ⟨fun _ => 0, fun _ => le_rfl, tendsto_const_nhds, ?_⟩
    intro r _ _ z hz _ _
    have hwext : wExt w C = w := by ext y; simp [wExt, htop]
    rw [hwext]
    have hgen := hw_gen z hz (by rw [htop]; exact ENNReal.ofReal_lt_top)
    have ⟨hint, hge⟩ := generator_eq_bv X hBV hgen.1
    exact ⟨hint, by linarith [hgen.2]⟩
  · set c₀ := C.toReal
    have hc₀ : 0 < c₀ := ENNReal.toReal_pos (ne_of_gt hC) htop
    have hd : 0 < X.drift := drift_pos X hX hBV
    obtain ⟨L, hL1, hL⟩ :=
      deriv_w_bdd_near_C X hX hBV hq hC htop hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
    have hmono := wExt_mono hw_cont hw0 hw_neg hw_smooth hw_grad
    have hnonneg := wExt_nonneg hw_cont hw0 hw_neg hw_smooth hw_grad
    set δ₀ := min (c₀ / 4) (1 / 2)
    have hδ₀_pos : 0 < δ₀ := lt_min (by linarith) (by norm_num)
    have hδ₀_le_c4 : δ₀ ≤ c₀ / 4 := min_le_left _ _
    have hδ₀_lt1 : δ₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hnu_tail : X.ν (Iic (-δ₀)) < ⊤ := nu_Iic_neg_lt_top X hδ₀_pos
    have hint_small_abs : IntegrableOn (fun u : ℝ => |u|) (Ioo (-δ₀) 0) X.ν :=
      (nu_Ioo_abs_integrable X hBV).mono_set (fun u hu => ⟨by linarith [hu.1, hδ₀_lt1], hu.2⟩)
    let η : ℝ → ℝ := fun r =>
      if r ≤ 0 then 0 else
        let r' := min r (c₀ / 8)
        (∫ u in Ioo (-δ₀) 0, min (2 * L * |u|) (4 * L * r') ∂X.ν) +
        (∫ u in Iic (-δ₀), (wExt w C (c₀ + r' + u) - wExt w C (c₀ - r' + u)) ∂X.ν)
    have hη_nonneg : ∀ r, 0 ≤ η r := by
      intro r
      dsimp only [η]
      split_ifs with hr
      · exact le_rfl
      · push Not at hr
        have hr' : 0 < min r (c₀ / 8) := lt_min hr (by linarith)
        apply add_nonneg
        · apply integral_nonneg; intro u
          exact le_min (by positivity) (by positivity)
        · apply integral_nonneg; intro u
          have hle : c₀ - min r (c₀ / 8) + u ≤ c₀ + min r (c₀ / 8) + u := by linarith
          exact sub_nonneg.mpr (hmono hle)
    have hη_tendsto : Tendsto η (𝓝[>] 0) (𝓝 0) := by
      have heq : η =ᶠ[𝓝[>] 0] fun r =>
          (∫ u in Ioo (-δ₀) 0, min (2 * L * |u|) (4 * L * min r (c₀ / 8)) ∂X.ν) +
          (∫ u in Iic (-δ₀), (wExt w C (c₀ + min r (c₀ / 8) + u) - wExt w C (c₀ - min r (c₀ / 8) + u)) ∂X.ν) := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        have hr' : ¬ (r ≤ 0) := not_le.mpr (mem_Ioi.mp hr)
        simp [η, hr']
      rw [tendsto_congr' heq]
      have hpart1 : Tendsto (fun r => ∫ u in Ioo (-δ₀) 0, min (2 * L * |u|) (4 * L * min r (c₀ / 8)) ∂X.ν)
          (𝓝[>] 0) (𝓝 0) := by
        suffices h : Tendsto (fun r => ∫ u in Ioo (-δ₀) 0, min (2 * L * |u|) (4 * L * min r (c₀ / 8)) ∂X.ν)
            (𝓝[>] 0) (𝓝 (∫ _ in Ioo (-δ₀) 0, (0 : ℝ) ∂X.ν)) by simpa using h
        refine tendsto_integral_filter_of_dominated_convergence (fun u => 2 * L * |u|) ?_ ?_ ?_ ?_
        · exact Eventually.of_forall (fun r =>
            ((continuous_const.mul continuous_abs).min continuous_const).aestronglyMeasurable)
        · filter_upwards [self_mem_nhdsWithin] with r hr
          filter_upwards with u
          have hr' : 0 ≤ min r (c₀ / 8) := le_min (le_of_lt (mem_Ioi.mp hr)) (by linarith)
          rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) (by positivity))]
          exact min_le_left _ _
        · exact hint_small_abs.const_mul (2 * L)
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u _
          have hmin : Tendsto (fun r : ℝ => 4 * L * min r (c₀ / 8)) (𝓝[>] 0) (𝓝 0) := by
            have h1 : Tendsto (fun r : ℝ => min r (c₀ / 8)) (𝓝[>] 0) (𝓝 (min 0 (c₀ / 8))) :=
              (continuous_id.min continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
            rw [min_eq_left (le_of_lt (by linarith))] at h1
            simpa using h1.const_mul (4 * L)
          have h2 : Tendsto (fun r : ℝ => min (2 * L * |u|) (4 * L * min r (c₀ / 8))) (𝓝[>] 0)
              (𝓝 (min (2 * L * |u|) 0)) := tendsto_const_nhds.min hmin
          rwa [min_eq_right (by positivity)] at h2
      have hpart2 : Tendsto (fun r => ∫ u in Iic (-δ₀), (wExt w C (c₀ + min r (c₀ / 8) + u) - wExt w C (c₀ - min r (c₀ / 8) + u)) ∂X.ν)
          (𝓝[>] 0) (𝓝 0) := by
        suffices h : Tendsto (fun r => ∫ u in Iic (-δ₀), (wExt w C (c₀ + min r (c₀ / 8) + u) - wExt w C (c₀ - min r (c₀ / 8) + u)) ∂X.ν)
            (𝓝[>] 0) (𝓝 (∫ _ in Iic (-δ₀), (0 : ℝ) ∂X.ν)) by simpa using h
        refine tendsto_integral_filter_of_dominated_convergence (fun _ => wExt w C (c₀ + c₀ / 8)) ?_ ?_ ?_ ?_
        · exact Eventually.of_forall (fun r =>
            ((hmono.measurable.comp (measurable_const.add measurable_id)).sub
              (hmono.measurable.comp (measurable_const.add measurable_id))).aestronglyMeasurable)
        · filter_upwards [self_mem_nhdsWithin] with r hr
          filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
          have hr' : 0 < min r (c₀ / 8) := lt_min (mem_Ioi.mp hr) (by linarith)
          have hle1 : 0 ≤ wExt w C (c₀ + min r (c₀ / 8) + u) - wExt w C (c₀ - min r (c₀ / 8) + u) :=
            sub_nonneg.mpr (hmono (by linarith))
          rw [Real.norm_eq_abs, abs_of_nonneg hle1]
          have hle2 : wExt w C (c₀ + min r (c₀ / 8) + u) ≤ wExt w C (c₀ + c₀ / 8) :=
            hmono (by linarith [min_le_right r (c₀ / 8), mem_Iic.mp hu])
          linarith [hnonneg (c₀ - min r (c₀ / 8) + u)]
        · exact integrableOn_const_of_lt_top hnu_tail _
        · have hnull : X.ν {-c₀} = 0 := nu_ac_volume X hX hBV (by simp)
          have hae_ne : ∀ᵐ u ∂(X.ν.restrict (Iic (-δ₀))), u ≠ -c₀ := by
            rw [ae_iff]
            have : {u | ¬ u ≠ -c₀} = {-c₀} := by ext u; simp
            rw [this, Measure.restrict_apply (measurableSet_singleton _)]
            exact measure_mono_null inter_subset_left hnull
          filter_upwards [hae_ne] with u hu
          have hmin : Tendsto (fun r : ℝ => min r (c₀ / 8)) (𝓝[>] 0) (𝓝 0) := by
            have h1 : Tendsto (fun r : ℝ => min r (c₀ / 8)) (𝓝[>] 0) (𝓝 (min 0 (c₀ / 8))) :=
              (continuous_id.min continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
            rwa [min_eq_left (by linarith)] at h1
          have hcont_at : ContinuousAt (wExt w C) (c₀ + u) := by
            by_cases hpos : 0 < c₀ + u
            · exact (wExt_continuousOn hw_cont).continuousAt (Ici_mem_nhds hpos)
            · have hneg : c₀ + u < 0 := lt_of_le_of_ne (not_lt.mp hpos) (by intro h; apply hu; linarith)
              apply ContinuousAt.congr_of_eventuallyEq (continuousAt_const (y := (0 : ℝ)))
              filter_upwards [isOpen_Iio.mem_nhds hneg] with y hy
              exact wExt_eq_zero_of_neg (C := C) hw_neg (mem_Iio.mp hy)
          have ht1 : Tendsto (fun r => wExt w C (c₀ + min r (c₀ / 8) + u)) (𝓝[>] 0) (𝓝 (wExt w C (c₀ + u))) :=
            hcont_at.tendsto.comp (by simpa using (tendsto_const_nhds.add hmin).add tendsto_const_nhds)
          have ht2 : Tendsto (fun r => wExt w C (c₀ - min r (c₀ / 8) + u)) (𝓝[>] 0) (𝓝 (wExt w C (c₀ + u))) :=
            hcont_at.tendsto.comp (by simpa using (tendsto_const_nhds.sub hmin).add tendsto_const_nhds)
          simpa using ht1.sub ht2
      simpa using hpart1.add hpart2
    refine ⟨η, hη_nonneg, hη_tendsto, ?_⟩
    intro r hr hr8 z hz hz_lt hz_ne
    have hr_lt : r < c₀ / 8 := hr8 htop
    have hz_lt' : z < c₀ + r := hz_lt.resolve_left htop
    have hz_ne' : z ≠ c₀ := hz_ne htop
    by_cases hzc : z < c₀
    · have hzw : wExt w C =ᶠ[𝓝 z] w := by
        filter_upwards [isOpen_Iio.mem_nhds hzc] with y hy
        exact wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr (le_of_lt (mem_Iio.mp hy)))
      have hderiv : deriv (wExt w C) z = deriv w z := hzw.deriv_eq
      have hgen := hw_gen z hz ((ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hz) htop).mpr hzc)
      have ⟨hint, hge⟩ := generator_eq_bv X hBV hgen.1
      have hfun_eq : EqOn (fun u => wExt w C (z + u) - wExt w C z) (fun u => w (z + u) - w z) (Iio (0 : ℝ)) := by
        intro u hu
        dsimp only
        have hzu : z + u < c₀ := by linarith [mem_Iio.mp hu]
        have hzuC : ENNReal.ofReal (z + u) ≤ C := by
          by_cases hneg : z + u ≤ 0
          · rw [ENNReal.ofReal_of_nonpos hneg]; exact zero_le
          · exact (ENNReal.ofReal_le_iff_le_toReal htop).mpr (le_of_lt hzu)
        rw [wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr (le_of_lt hzc)),
            wExt_eq_of_le hzuC]
      refine ⟨(integrableOn_congr_fun hfun_eq measurableSet_Iio).mpr hint, ?_⟩
      rw [hderiv, setIntegral_congr_fun measurableSet_Iio hfun_eq,
          wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr (le_of_lt hzc))]
      linarith [hgen.2, hη_nonneg r]
    · have hzc' : c₀ < z := lt_of_le_of_ne (not_lt.mp hzc) (Ne.symm hz_ne')
      have hderiv : deriv (wExt w C) z = 1 := by
        have heq : wExt w C =ᶠ[𝓝 z] fun y => w c₀ + (y - c₀) := by
          filter_upwards [isOpen_Ioi.mem_nhds hzc'] with y hy
          have hy' : ¬ y ≤ C.toReal := not_le.mpr (mem_Ioi.mp hy)
          simp [wExt, htop, hy', c₀]
        rw [heq.deriv_eq]
        have hd1 : HasDerivAt (fun y => w c₀ + (y - c₀)) (0 + 1) z :=
          (hasDerivAt_const z (w c₀)).add ((hasDerivAt_id z).sub_const c₀)
        rw [zero_add] at hd1
        exact hd1.deriv
      have hsplit : Iio (0 : ℝ) = Iic (-δ₀) ∪ Ioo (-δ₀) 0 := by
        ext u; simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]; constructor
        · intro hu; by_cases h : u ≤ -δ₀
          · exact Or.inl h
          · exact Or.inr ⟨by linarith, hu⟩
        · rintro (h | ⟨_, h⟩) <;> linarith
      have hdisj : Disjoint (Iic (-δ₀)) (Ioo (-δ₀) 0) := by
        rw [Set.disjoint_left]; intro u h1 h2; linarith [mem_Iic.mp h1, h2.1]
      have hint_z : IntegrableOn (fun u => wExt w C (z + u) - wExt w C z) (Iio (0 : ℝ)) X.ν := by
        rw [hsplit]
        refine IntegrableOn.union ?_ ?_
        · refine (integrableOn_const_of_lt_top hnu_tail (wExt w C z)).mono'
            ((hmono.measurable.comp (measurable_const.add measurable_id)).sub
              measurable_const).aestronglyMeasurable ?_
          filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
          have hle : wExt w C (z + u) ≤ wExt w C z := hmono (by linarith [mem_Iic.mp hu])
          rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
          linarith [hnonneg (z + u)]
        · refine (hint_small_abs.const_mul L).mono'
            ((hmono.measurable.comp (measurable_const.add measurable_id)).sub
              measurable_const).aestronglyMeasurable ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
          have hle : wExt w C (z + u) ≤ wExt w C z := hmono (by linarith [hu.2])
          have hlip := wExt_lipschitz_above_half_C hC htop hw_cont hw_smooth hL1 hL
            (a := z + u) (b := z) (by linarith [hu.1, hδ₀_le_c4]) (by linarith [hu.2])
          rw [Real.norm_eq_abs, abs_of_nonpos (by linarith), abs_of_neg hu.2]
          linarith
      refine ⟨hint_z, ?_⟩
      set y := c₀ - r
      have hy_pos : 0 < y := by linarith
      have hy_lt : y < c₀ := by linarith
      have hgen_y := hw_gen y hy_pos ((ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy_pos) htop).mpr hy_lt)
      have ⟨hint_y, hge_y⟩ := generator_eq_bv X hBV hgen_y.1
      have hwy_grad : 1 ≤ deriv w y := hw_grad y hy_pos ((ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy_pos) htop).mpr hy_lt)
      have hwy_le_wz : w y ≤ wExt w C z := by
        have := hmono (show y ≤ z by linarith)
        rwa [wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr (le_of_lt hy_lt))] at this
      have hdiff_le : X.drift * deriv (wExt w C) z +
          (∫ u in Iio (0 : ℝ), (wExt w C (z + u) - wExt w C z) ∂X.ν) - q * wExt w C z ≤
          ∫ u in Iio (0 : ℝ), ((wExt w C (z + u) - wExt w C z) - (w (y + u) - w y)) ∂X.ν := by
        rw [hderiv, integral_sub hint_z hint_y]
        have h1 : X.drift * 1 ≤ X.drift * deriv w y := mul_le_mul_of_nonneg_left hwy_grad (le_of_lt hd)
        have h2 : q * w y ≤ q * wExt w C z := mul_le_mul_of_nonneg_left hwy_le_wz (le_of_lt hq)
        linarith [hgen_y.2]
      refine le_trans hdiff_le ?_
      have hr_not_le : ¬ (r ≤ 0) := not_le.mpr hr
      have hmin_r : min r (c₀ / 8) = r := min_eq_left (le_of_lt hr_lt)
      simp only [η, hr_not_le, ↓reduceIte, hmin_r]
      have hint_zy : IntegrableOn (fun u => (wExt w C (z + u) - wExt w C z) - (w (y + u) - w y))
          (Iio (0 : ℝ)) X.ν := hint_z.sub hint_y
      rw [hsplit, setIntegral_union hdisj measurableSet_Ioo
        (hint_zy.mono_set (fun u hu => lt_of_le_of_lt hu (neg_lt_zero.mpr hδ₀_pos)))
        (hint_zy.mono_set (fun u hu => hu.2)), add_comm]
      apply add_le_add
      · apply setIntegral_mono_on
          (hint_zy.mono_set (fun u hu => hu.2))
          (Integrable.mono' (g := fun u => 2 * L * |u|) (f := fun u => min (2 * L * |u|) (4 * L * r))
            (hint_small_abs.const_mul (2 * L))
            (((continuous_const.mul continuous_abs).min continuous_const).aestronglyMeasurable)
            (ae_of_all _ (fun u => by
              have hnn1 : 0 ≤ 2 * L * |u| := mul_nonneg (by linarith) (abs_nonneg u)
              have hnn2 : 0 ≤ 4 * L * r := mul_nonneg (by linarith) (le_of_lt hr)
              rw [Real.norm_eq_abs, abs_of_nonneg (le_min hnn1 hnn2)]
              exact min_le_left _ _)))
          measurableSet_Ioo
        intro u hu
        have hwy_eq : w y = wExt w C y :=
          (wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr (le_of_lt hy_lt))).symm
        have hwyu_eq : w (y + u) = wExt w C (y + u) :=
          (wExt_eq_of_le (by
            by_cases hneg : y + u ≤ 0
            · rw [ENNReal.ofReal_of_nonpos hneg]; exact zero_le
            · exact (ENNReal.ofReal_le_iff_le_toReal htop).mpr (by linarith [hu.2]))).symm
        rw [hwy_eq, hwyu_eq]
        have hlip1 := wExt_lipschitz_above_half_C hC htop hw_cont hw_smooth hL1 hL
          (a := y + u) (b := y) (by linarith [hu.1, hδ₀_le_c4]) (by linarith [hu.2])
        have hlip2 := wExt_lipschitz_above_half_C hC htop hw_cont hw_smooth hL1 hL
          (a := y + u) (b := z + u) (by linarith [hu.1, hδ₀_le_c4]) (by linarith)
        have hmono1 : wExt w C (z + u) ≤ wExt w C z := hmono (by linarith [hu.2])
        have hmono2 : wExt w C y ≤ wExt w C z := hmono (by linarith)
        have habs : |u| = -u := abs_of_neg hu.2
        have hLu : L * (y - (y + u)) = L * |u| := by rw [habs]; ring
        have hpos_Lu : 0 ≤ L * |u| := mul_nonneg (by linarith) (abs_nonneg u)
        have hpos_Lr : 0 ≤ L * r := mul_nonneg (by linarith) (le_of_lt hr)
        have hzy : L * ((z + u) - (y + u)) ≤ 2 * L * r := by
          calc L * ((z + u) - (y + u))
              ≤ L * (2 * r) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
            _ = 2 * L * r := by ring
        apply le_min <;> linarith
      · apply setIntegral_mono_on
          (hint_zy.mono_set (fun u hu => lt_of_le_of_lt hu (neg_lt_zero.mpr hδ₀_pos)))
          (Integrable.mono' (g := fun _ => wExt w C (c₀ + r))
            (f := fun u => wExt w C (c₀ + r + u) - wExt w C (c₀ - r + u))
            (integrableOn_const_of_lt_top hnu_tail (wExt w C (c₀ + r)))
            ((hmono.measurable.comp (measurable_const.add measurable_id)).sub
              (hmono.measurable.comp (measurable_const.add measurable_id))).aestronglyMeasurable
            (by
              filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
              have hle1 : 0 ≤ wExt w C (c₀ + r + u) - wExt w C (c₀ - r + u) :=
                sub_nonneg.mpr (hmono (by linarith))
              rw [Real.norm_eq_abs, abs_of_nonneg hle1]
              have hle2 : wExt w C (c₀ + r + u) ≤ wExt w C (c₀ + r) :=
                hmono (by linarith [mem_Iic.mp hu])
              linarith [hnonneg (c₀ - r + u)]))
          measurableSet_Iic
        intro u hu
        have hwy_eq : w y = wExt w C y :=
          (wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr (le_of_lt hy_lt))).symm
        have hwyu_eq : w (y + u) = wExt w C (y + u) :=
          (wExt_eq_of_le (by
            by_cases hneg : y + u ≤ 0
            · rw [ENNReal.ofReal_of_nonpos hneg]; exact zero_le
            · exact (ENNReal.ofReal_le_iff_le_toReal htop).mpr (by linarith [mem_Iic.mp hu]))).symm
        rw [hwy_eq, hwyu_eq]
        have h1 : wExt w C (z + u) ≤ wExt w C (c₀ + r + u) := hmono (by linarith)
        have h2 : wExt w C y ≤ wExt w C z := hmono (by linarith)
        linarith

/-! ### Section 3: Truncated double-Steklov regularization -/

private def steklov (δ : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  (1 / δ) * ∫ s in (0 : ℝ)..δ, g (y + s)

private lemma steklov_eq_setIntegral {δ : ℝ} (hδ : 0 < δ) (g : ℝ → ℝ) (y : ℝ) :
    steklov δ g y = (1 / δ) * ∫ s in Ioo (0 : ℝ) δ, g (y + s) := by
  unfold steklov
  rw [intervalIntegral.integral_of_le hδ.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]

private lemma steklov_continuous {δ : ℝ} (_hδ : 0 < δ) {g : ℝ → ℝ} (hg_mono : Monotone g) :
    Continuous (steklov δ g) := by
  have heq : steklov δ g = fun y => (1 / δ) * ((∫ u in (0 : ℝ)..(y + δ), g u) - (∫ u in (0 : ℝ)..(y + 0), g u)) := by
    ext y
    unfold steklov
    congr 1
    rw [intervalIntegral.integral_comp_add_left g y, add_zero]
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (a := (0 : ℝ)) (b := y) (c := y + δ) (hg_mono.intervalIntegrable (μ := volume)) (hg_mono.intervalIntegrable (μ := volume))
    linarith
  rw [heq]
  have hprim : ∀ c : ℝ, Continuous (fun y : ℝ => ∫ u in (0 : ℝ)..(y + c), g u) := by
    intro c
    rw [continuous_iff_continuousAt]
    intro y₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    set K := max (|g (y₀ + c - 1)|) (|g (y₀ + c + 1)|) + 1
    have hK : 0 < K := by positivity
    refine ⟨min 1 (ε / K), lt_min zero_lt_one (div_pos hε hK), ?_⟩
    intro y hy
    rw [Real.dist_eq] at hy ⊢
    have hy1 : |y - y₀| < 1 := lt_of_lt_of_le hy (min_le_left _ _)
    have hy2 : |y - y₀| < ε / K := lt_of_lt_of_le hy (min_le_right _ _)
    have hdiff : (∫ u in (0 : ℝ)..(y + c), g u) - (∫ u in (0 : ℝ)..(y₀ + c), g u) =
        ∫ u in (y₀ + c)..(y + c), g u := by
      have h := intervalIntegral.integral_add_adjacent_intervals
        (a := (0 : ℝ)) (b := y₀ + c) (c := y + c) (hg_mono.intervalIntegrable (μ := volume)) (hg_mono.intervalIntegrable (μ := volume))
      linarith
    rw [hdiff]
    have hbound : ∀ u ∈ Set.uIoc (y₀ + c) (y + c), ‖g u‖ ≤ K := by
      intro u hu
      rw [Set.uIoc_eq_union, mem_union, mem_Ioc, mem_Ioc] at hu
      have hlo : y₀ + c - 1 ≤ u := by rcases hu with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith [abs_lt.mp hy1]
      have hhi : u ≤ y₀ + c + 1 := by rcases hu with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith [abs_lt.mp hy1]
      have hgle1 : g (y₀ + c - 1) ≤ g u := hg_mono hlo
      have hgle2 : g u ≤ g (y₀ + c + 1) := hg_mono hhi
      rw [Real.norm_eq_abs]
      have : |g u| ≤ max (|g (y₀ + c - 1)|) (|g (y₀ + c + 1)|) := by
        rw [abs_le]
        exact ⟨by linarith [neg_abs_le (g (y₀ + c - 1)), le_max_left (|g (y₀ + c - 1)|) (|g (y₀ + c + 1)|)],
               by linarith [le_abs_self (g (y₀ + c + 1)), le_max_right (|g (y₀ + c - 1)|) (|g (y₀ + c + 1)|)]⟩
      linarith
    have hint_norm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs] at hint_norm
    have hlen : |(y + c) - (y₀ + c)| = |y - y₀| := by ring_nf
    rw [hlen] at hint_norm
    calc |∫ u in (y₀ + c)..(y + c), g u| ≤ K * |y - y₀| := hint_norm
      _ < K * (ε / K) := mul_lt_mul_of_pos_left hy2 hK
      _ = ε := mul_div_cancel₀ ε (ne_of_gt hK)
  exact continuous_const.mul ((hprim δ).sub (hprim 0))

private lemma steklov_hasDerivAt_of_continuousOn {δ a : ℝ} (hδ : 0 < δ) {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Ici a)) {y : ℝ} (hy : a < y) :
    HasDerivAt (steklov δ g) ((g (y + δ) - g y) / δ) y := by
  let gExt : ℝ → ℝ := fun u => g (max u a)
  have hgExt_cont : Continuous gExt :=
    hg_cont.comp_continuous (continuous_id.max continuous_const) (fun u => le_max_right u a)
  have heq : steklov δ g =ᶠ[𝓝 y] fun z => (1 / δ) * ((∫ u in a..(z + δ), gExt u) - (∫ u in a..z, gExt u)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    unfold steklov
    congr 1
    have hz' : a < z := mem_Ioi.mp hz
    have hcongr : ∫ s in (0 : ℝ)..δ, g (z + s) = ∫ s in (0 : ℝ)..δ, gExt (z + s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hδ.le] at hs
      simp only [gExt, max_eq_left (show a ≤ z + s by linarith [hs.1])]
    rw [hcongr, intervalIntegral.integral_comp_add_left gExt z, add_zero]
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (a := a) (b := z) (c := z + δ)
      (hgExt_cont.intervalIntegrable (μ := volume) _ _)
      (hgExt_cont.intervalIntegrable (μ := volume) _ _)
    linarith
  have hd1 : HasDerivAt (fun z => ∫ u in a..(z + δ), gExt u) (gExt (y + δ)) y := by
    have hc := (hgExt_cont.integral_hasStrictDerivAt a (y + δ)).hasDerivAt.comp y
      ((hasDerivAt_id y).add_const δ)
    rwa [mul_one] at hc
  have hd2 : HasDerivAt (fun z => ∫ u in a..z, gExt u) (gExt y) y :=
    (hgExt_cont.integral_hasStrictDerivAt a y).hasDerivAt
  have hd3 : HasDerivAt (fun z => (1 / δ) * ((∫ u in a..(z + δ), gExt u) - (∫ u in a..z, gExt u)))
      ((1 / δ) * (gExt (y + δ) - gExt y)) y :=
    (hd1.sub hd2).const_mul (1 / δ)
  have hgy1 : gExt (y + δ) = g (y + δ) := by simp [gExt, max_eq_left (by linarith : a ≤ y + δ)]
  have hgy2 : gExt y = g y := by simp [gExt, max_eq_left (le_of_lt hy)]
  rw [hgy1, hgy2, one_div_mul_eq_div] at hd3
  exact hd3.congr_of_eventuallyEq heq

private lemma steklov_hasDerivAt_global {δ : ℝ} (hδ : 0 < δ) {g : ℝ → ℝ}
    (hg_cont : Continuous g) (y : ℝ) :
    HasDerivAt (steklov δ g) ((g (y + δ) - g y) / δ) y :=
  steklov_hasDerivAt_of_continuousOn hδ hg_cont.continuousOn (sub_one_lt y)

private lemma monotone_shift_integrableOn {δ : ℝ} {g : ℝ → ℝ} (hg : Monotone g) (y : ℝ) :
    IntegrableOn (fun s => g (y + s)) (Ioo (0 : ℝ) δ) volume := by
  have hm : Monotone (fun s : ℝ => g (y + s)) := fun a b hab => hg (by linarith)
  exact (hm.intervalIntegrable (μ := volume) (a := 0) (b := δ)).1.mono_set Ioo_subset_Ioc_self

private lemma steklov_step (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    {q δ a b_max B₀ L_g E_err y_bad : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (ha1 : a / 2 < 1) (_hb : 0 ≤ b_max) (_hL_g : 0 ≤ L_g)
    {g : ℝ → ℝ}
    (hg_mono : Monotone g) (hg_nonneg : ∀ y, 0 ≤ g y) (hg_bdd : ∀ y, g y ≤ B₀)
    (hg_cont : ContinuousOn g (Ici (-a)))
    (hg_lip : ∀ u v, -a / 2 ≤ u → u ≤ v → g v - g u ≤ L_g * (v - u))
    (hg_ftc : ∀ z ∈ Icc (0 : ℝ) b_max,
      IntegrableOn (fun s => deriv g (z + s)) (Ioo (0 : ℝ) δ) volume ∧
      ∫ s in Ioo (0 : ℝ) δ, deriv g (z + s) = g (z + δ) - g z)
    (hg_gen : ∀ y ∈ Ioo (0 : ℝ) (b_max + δ), y ≠ y_bad →
      IntegrableOn (fun u => g (y + u) - g y) (Iio (0 : ℝ)) X.ν ∧
      X.drift * deriv g y + ∫ u in Iio (0 : ℝ), (g (y + u) - g y) ∂X.ν - q * g y ≤ E_err) :
    let G := steklov δ g
    Monotone G ∧ (∀ y, 0 ≤ G y) ∧ (∀ y, G y ≤ B₀) ∧ Continuous G ∧
    (∀ u v, -a / 2 ≤ u → u ≤ v → G v - G u ≤ L_g * (v - u)) ∧
    (∀ z ∈ Icc (0 : ℝ) b_max,
      IntegrableOn (fun u => G (z + u) - G z) (Iio (0 : ℝ)) X.ν ∧
      X.drift * deriv G z + ∫ u in Iio (0 : ℝ), (G (z + u) - G z) ∂X.ν - q * G z ≤ E_err) := by
  intro G
  have h_int_shift : ∀ y : ℝ, IntegrableOn (fun s => g (y + s)) (Ioo (0 : ℝ) δ) volume :=
    monotone_shift_integrableOn hg_mono
  have hG_mono : Monotone G := by
    intro u v huv
    simp only [G, steklov_eq_setIntegral hδ]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply setIntegral_mono_on (h_int_shift u) (h_int_shift v) measurableSet_Ioo
    intro s _; exact hg_mono (by linarith)
  have hG_nonneg : ∀ y, 0 ≤ G y := by
    intro y; simp only [G, steklov_eq_setIntegral hδ]
    exact mul_nonneg (by positivity) (integral_nonneg fun s => hg_nonneg _)
  have hG_bdd : ∀ y, G y ≤ B₀ := by
    intro y; simp only [G, steklov_eq_setIntegral hδ]
    have hle : ∫ s in Ioo (0 : ℝ) δ, g (y + s) ≤ ∫ _ in Ioo (0 : ℝ) δ, B₀ := by
      apply setIntegral_mono_on (h_int_shift y)
        (integrableOn_const_of_lt_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) B₀) measurableSet_Ioo
      intro s _; exact hg_bdd _
    have hconst : ∫ _ in Ioo (0 : ℝ) δ, B₀ = δ * B₀ := by
      rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioo, sub_zero,
          ENNReal.toReal_ofReal hδ.le]
    rw [hconst] at hle
    calc (1 / δ) * ∫ s in Ioo (0 : ℝ) δ, g (y + s) ≤ (1 / δ) * (δ * B₀) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = B₀ := by field_simp [hδ.ne']
  have hG_cont : Continuous G := steklov_continuous hδ hg_mono
  have hG_lip : ∀ u v, -a / 2 ≤ u → u ≤ v → G v - G u ≤ L_g * (v - u) := by
    intro u v hu huv
    simp only [G, steklov_eq_setIntegral hδ]
    rw [← mul_sub, ← integral_sub (h_int_shift v) (h_int_shift u)]
    have hle : ∫ s in Ioo (0 : ℝ) δ, (g (v + s) - g (u + s)) ≤ ∫ _ in Ioo (0 : ℝ) δ, L_g * (v - u) := by
      apply setIntegral_mono_on ((h_int_shift v).sub (h_int_shift u))
        (integrableOn_const_of_lt_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) _) measurableSet_Ioo
      intro s hs
      change g (v + s) - g (u + s) ≤ L_g * (v - u)
      have : (v + s) - (u + s) = v - u := by ring
      linarith [hg_lip (u + s) (v + s) (by linarith [hs.1]) (by linarith)]
    have hconst : ∫ _ in Ioo (0 : ℝ) δ, L_g * (v - u) = δ * (L_g * (v - u)) := by
      rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioo, sub_zero,
          ENNReal.toReal_ofReal hδ.le]
    rw [hconst] at hle
    calc (1 / δ) * ∫ s in Ioo (0 : ℝ) δ, (g (v + s) - g (u + s))
        ≤ (1 / δ) * (δ * (L_g * (v - u))) := mul_le_mul_of_nonneg_left hle (by positivity)
      _ = L_g * (v - u) := by field_simp [hδ.ne']
  refine ⟨hG_mono, hG_nonneg, hG_bdd, hG_cont, hG_lip, ?_⟩
  intro z hz
  have : SigmaFinite X.ν := nu_sigmaFinite X
  set μs : Measure ℝ := volume.restrict (Ioo (0 : ℝ) δ)
  set μu : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  have : IsFiniteMeasure μs := ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  let Φ : ℝ × ℝ → ℝ := fun p => g (z + p.1 + p.2) - g (z + p.1)
  have hΦ_meas : Measurable Φ :=
    (hg_mono.measurable.comp ((measurable_const.add measurable_fst).add measurable_snd)).sub
      (hg_mono.measurable.comp (measurable_const.add measurable_fst))
  let ψ : ℝ → ℝ := (Iic (-a / 2)).indicator (fun _ => B₀) + (Ioo (-a / 2) 0).indicator (fun u => L_g * |u|)
  have hψ_int : Integrable ψ μu := by
    refine Integrable.add ?_ ?_
    · rw [integrable_indicator_iff measurableSet_Iic]
      have hfin : X.ν (Iic (-a / 2)) < ⊤ := by
        have : -a / 2 = -(a / 2) := by ring
        rw [this]; exact nu_Iic_neg_lt_top X (half_pos ha)
      exact integrableOn_const_of_lt_top (by
        rw [Measure.restrict_apply measurableSet_Iic]
        exact lt_of_le_of_lt (measure_mono inter_subset_left) hfin) B₀
    · rw [integrable_indicator_iff measurableSet_Ioo]
      have hsub : Ioo (-a / 2) 0 ∩ Iio 0 = Ioo (-a / 2) 0 := inter_eq_left.mpr (fun u hu => hu.2)
      rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioo, hsub]
      exact ((nu_Ioo_abs_integrable X hBV).mono_set (fun u hu => ⟨by linarith [hu.1], hu.2⟩)).const_mul L_g
  have hdom_prod : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * ψ p.2) (μs.prod μu) :=
    (integrable_const (1 : ℝ)).mul_prod hψ_int
  have hΦ_int : Integrable Φ (μs.prod μu) := by
    refine hdom_prod.mono' hΦ_meas.aestronglyMeasurable ?_
    have hae_s : ∀ᵐ p ∂(μs.prod μu), p.1 ∈ Ioo (0 : ℝ) δ :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (ae_restrict_mem measurableSet_Ioo)
    have hae_u : ∀ᵐ p ∂(μs.prod μu), p.2 ∈ Iio (0 : ℝ) :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd (ae_restrict_mem measurableSet_Iio)
    filter_upwards [hae_s, hae_u] with p hs hu
    have hle : g (z + p.1 + p.2) ≤ g (z + p.1) := hg_mono (by linarith [mem_Iio.mp hu])
    rw [Real.norm_eq_abs, abs_of_nonpos (show Φ p ≤ 0 by dsimp [Φ]; linarith)]
    simp only [Φ, neg_sub, one_mul, ψ, Pi.add_apply]
    by_cases hcase : p.2 ≤ -a / 2
    · have h1 : p.2 ∈ Iic (-a / 2) := hcase
      have h2 : p.2 ∉ Ioo (-a / 2) 0 := fun hc => by linarith [hc.1]
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]
      linarith [hg_bdd (z + p.1), hg_nonneg (z + p.1 + p.2)]
    · push Not at hcase
      have h1 : p.2 ∉ Iic (-a / 2) := not_le.mpr hcase
      have h2 : p.2 ∈ Ioo (-a / 2) 0 := ⟨hcase, hu⟩
      rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add, abs_of_neg hu]
      have hlip := hg_lip (z + p.1 + p.2) (z + p.1) (by linarith [hz.1, hs.1]) (by linarith [mem_Iio.mp hu])
      linarith
  have hfub : ∫ s in Ioo (0 : ℝ) δ, (∫ u in Iio (0 : ℝ), Φ (s, u) ∂X.ν) =
      ∫ u in Iio (0 : ℝ), (∫ s in Ioo (0 : ℝ) δ, Φ (s, u)) ∂X.ν := by
    change ∫ s, (∫ u, Φ (s, u) ∂μu) ∂μs = ∫ u, (∫ s, Φ (s, u) ∂μs) ∂μu
    rw [← MeasureTheory.integral_prod Φ hΦ_int, MeasureTheory.integral_prod_symm Φ hΦ_int]
  have hG_diff_eq : ∀ u : ℝ, G (z + u) - G z = (1 / δ) * ∫ s in Ioo (0 : ℝ) δ, Φ (s, u) := by
    intro u
    simp only [G, steklov_eq_setIntegral hδ, ← mul_sub]
    congr 1
    rw [← integral_sub (h_int_shift (z + u)) (h_int_shift z)]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro s _; dsimp [Φ]; ring_nf
  have hint_G : IntegrableOn (fun u => G (z + u) - G z) (Iio (0 : ℝ)) X.ν := by
    change Integrable (fun u => G (z + u) - G z) μu
    simp_rw [hG_diff_eq]
    exact (hΦ_int.swap.integral_prod_left).const_mul (1 / δ)
  refine ⟨hint_G, ?_⟩
  have hderiv_G : deriv G z = (1 / δ) * ∫ s in Ioo (0 : ℝ) δ, deriv g (z + s) := by
    rw [(steklov_hasDerivAt_of_continuousOn hδ hg_cont (by linarith [hz.1] : -a < z)).deriv,
        (hg_ftc z hz).2, one_div_mul_eq_div]
  have hint_jump_G : ∫ u in Iio (0 : ℝ), (G (z + u) - G z) ∂X.ν =
      (1 / δ) * ∫ s in Ioo (0 : ℝ) δ, (∫ u in Iio (0 : ℝ), Φ (s, u) ∂X.ν) := by
    simp_rw [hG_diff_eq]
    rw [integral_const_mul, hfub]
  have hG_val : G z = (1 / δ) * ∫ s in Ioo (0 : ℝ) δ, g (z + s) :=
    steklov_eq_setIntegral hδ g z
  rw [hderiv_G, hint_jump_G, hG_val]
  have hint1 : Integrable (fun s => X.drift * deriv g (z + s)) μs := (hg_ftc z hz).1.const_mul X.drift
  have hint2 : Integrable (fun s => ∫ u in Iio (0 : ℝ), Φ (s, u) ∂X.ν) μs := hΦ_int.integral_prod_left
  have hint3 : Integrable (fun s => q * g (z + s)) μs := (h_int_shift z).const_mul q
  have hcomb : X.drift * ((1 / δ) * ∫ s, deriv g (z + s) ∂μs) +
      (1 / δ) * (∫ s, (∫ u in Iio (0 : ℝ), Φ (s, u) ∂X.ν) ∂μs) -
      q * ((1 / δ) * ∫ s, g (z + s) ∂μs) =
      (1 / δ) * ∫ s, (X.drift * deriv g (z + s) + (∫ u in Iio (0 : ℝ), Φ (s, u) ∂X.ν) - q * g (z + s)) ∂μs := by
    have h_add : ∫ s, (X.drift * deriv g (z + s) + ∫ u in Iio (0 : ℝ), Φ (s, u) ∂X.ν) ∂μs =
        (∫ s, X.drift * deriv g (z + s) ∂μs) + ∫ s, (∫ u in Iio (0 : ℝ), Φ (s, u) ∂X.ν) ∂μs :=
      integral_add hint1 hint2
    have h12 : Integrable (fun s => X.drift * deriv g (z + s) + ∫ u in Iio (0 : ℝ), Φ (s, u) ∂X.ν) μs :=
      hint1.add hint2
    have h_sub : ∫ s, (X.drift * deriv g (z + s) + (∫ u in Iio (0 : ℝ), Φ (s, u) ∂X.ν) - q * g (z + s)) ∂μs =
        (∫ s, (X.drift * deriv g (z + s) + ∫ u in Iio (0 : ℝ), Φ (s, u) ∂X.ν) ∂μs) - ∫ s, q * g (z + s) ∂μs :=
      integral_sub h12 hint3
    rw [h_sub, h_add, integral_const_mul, integral_const_mul]
    ring
  change X.drift * ((1 / δ) * ∫ s, deriv g (z + s) ∂μs) +
      (1 / δ) * (∫ s, (∫ u in Iio (0 : ℝ), Φ (s, u) ∂X.ν) ∂μs) -
      q * ((1 / δ) * ∫ s, g (z + s) ∂μs) ≤ E_err
  rw [hcomb]
  have hae_ne : ∀ᵐ s ∂μs, s ≠ y_bad - z := by
    rw [ae_iff]
    have : {s | ¬ s ≠ y_bad - z} = {y_bad - z} := by ext s; simp
    rw [this, Measure.restrict_apply (measurableSet_singleton _)]
    exact measure_mono_null inter_subset_left Real.volume_singleton
  have hmono_int : ∫ s, (X.drift * deriv g (z + s) + (∫ u in Iio (0 : ℝ), Φ (s, u) ∂X.ν) - q * g (z + s)) ∂μs ≤
      ∫ _, E_err ∂μs := by
    apply integral_mono_ae ((hint1.add hint2).sub hint3) (integrable_const E_err)
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hae_ne] with s hs hne
    have hzs_mem : z + s ∈ Ioo (0 : ℝ) (b_max + δ) := ⟨by linarith [hz.1, hs.1], by linarith [hz.2, hs.2]⟩
    have hzs_ne : z + s ≠ y_bad := by intro hc; apply hne; linarith
    exact (hg_gen (z + s) hzs_mem hzs_ne).2
  have hconst_err : ∫ _, E_err ∂μs = δ * E_err := by
    rw [integral_const, smul_eq_mul, Measure.real_def, Measure.restrict_apply_univ,
        Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal hδ.le]
  rw [hconst_err] at hmono_int
  calc (1 / δ) * ∫ s, (X.drift * deriv g (z + s) + (∫ u in Iio (0 : ℝ), Φ (s, u) ∂X.ν) - q * g (z + s)) ∂μs
      ≤ (1 / δ) * (δ * E_err) := mul_le_mul_of_nonneg_left hmono_int (by positivity)
    _ = E_err := by field_simp [hδ.ne']

private lemma wExt_lipschitz_above_pos (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) {q : ℝ} (hq : 0 < q)
    {w : ℝ → ℝ} {C : ℝ≥0∞} (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    {r₀ M_cut : ℝ} (hr₀ : 0 < r₀) (hM : r₀ ≤ M_cut) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧
      (∀ y ∈ Ioo r₀ M_cut, (C ≠ ⊤ → y ≠ C.toReal) → deriv (wExt w C) y ≤ L₀) ∧
      (∀ u v : ℝ, r₀ ≤ u → u ≤ v → wExt w C (min v M_cut) - wExt w C (min u M_cut) ≤ L₀ * (v - u)) := by
  have hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    isOpen_Ioi.inter (isOpen_lt ENNReal.continuous_ofReal continuous_const)
  have hderiv_cont : ContinuousOn (deriv w) {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.continuousOn_deriv_of_isOpen hopen le_rfl
  by_cases htop : C = ⊤
  · have hsub : Icc r₀ M_cut ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
      intro y hy; exact ⟨lt_of_lt_of_le hr₀ hy.1, by rw [htop]; exact ENNReal.ofReal_lt_top⟩
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hderiv_cont.mono hsub)
    set L₀ := max 1 K
    have hL₀_deriv : ∀ y ∈ Icc r₀ M_cut, deriv w y ≤ L₀ := by
      intro y hy
      have hKy : |deriv w y| ≤ K := by simpa [Real.norm_eq_abs] using hK y hy
      exact (le_abs_self _).trans (hKy.trans (le_max_right 1 K))
    have hwext : wExt w C = w := by ext y; simp [wExt, htop]
    refine ⟨L₀, le_max_left 1 K, ?_, ?_⟩
    · intro y hy _; rw [hwext]; exact hL₀_deriv y ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    · intro u v hu huv
      rw [hwext]
      set u' := min u M_cut
      set v' := min v M_cut
      have hu' : r₀ ≤ u' := le_min hu hM
      have huv' : u' ≤ v' := min_le_min_right M_cut huv
      have hv' : v' ≤ M_cut := min_le_right v M_cut
      have hdiff_le : v' - u' ≤ v - u := by
        dsimp [u', v']
        cases le_total v M_cut with
        | inl hvM => rw [min_eq_left hvM, min_eq_left (le_trans huv hvM)]
        | inr hvM =>
          rw [min_eq_right hvM]
          cases le_total u M_cut with
          | inl huM => rw [min_eq_left huM]; linarith
          | inr huM => rw [min_eq_right huM]; linarith
      rcases eq_or_lt_of_le huv' with heq | hlt
      · rw [heq, sub_self]; exact mul_nonneg (by linarith [le_max_left 1 K]) (by linarith)
      · have hcont_seg : ContinuousOn w (Icc u' v') := hw_cont.mono (fun z hz => show 0 ≤ z by linarith [hz.1, hu', hr₀])
        have hdiff_seg : DifferentiableOn ℝ w (Ioo u' v') :=
          (hw_smooth.differentiableOn one_ne_zero).mono (fun z hz => hsub ⟨le_trans hu' (le_of_lt hz.1), le_trans (le_of_lt hz.2) hv'⟩)
        obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope w hlt hcont_seg hdiff_seg
        have hξ_le : deriv w ξ ≤ L₀ := hL₀_deriv ξ ⟨le_trans hu' (le_of_lt hξ.1), le_trans (le_of_lt hξ.2) hv'⟩
        rw [hslope, div_le_iff₀ (sub_pos.mpr hlt)] at hξ_le
        calc w v' - w u' ≤ L₀ * (v' - u') := hξ_le
          _ ≤ L₀ * (v - u) := mul_le_mul_of_nonneg_left hdiff_le (by linarith [le_max_left 1 K])
  · set c₀ := C.toReal
    have hc₀ : 0 < c₀ := ENNReal.toReal_pos (ne_of_gt hC) htop
    obtain ⟨L₁, hL₁_ge1, hL₁⟩ :=
      deriv_w_bdd_near_C X hX hBV hq hC htop hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
    set a_lo := min r₀ (c₀ / 2)
    have ha_lo_pos : 0 < a_lo := lt_min hr₀ (half_pos hc₀)
    have hsub_lo : Icc a_lo (c₀ / 2) ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
      intro y hy
      have hy_pos : 0 < y := lt_of_lt_of_le ha_lo_pos hy.1
      refine ⟨hy_pos,
        (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy_pos) htop).mpr (by linarith [hy.2])⟩
    obtain ⟨L₂, hL₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hderiv_cont.mono hsub_lo)
    set L₀ := max L₁ L₂
    have hL₀_ge1 : 1 ≤ L₀ := le_trans hL₁_ge1 (le_max_left L₁ L₂)
    have hderiv_le : ∀ y, r₀ ≤ y → y ≠ c₀ → deriv (wExt w C) y ≤ L₀ := by
      intro y hy hne
      by_cases hyc : y < c₀
      · have hzw : wExt w C =ᶠ[𝓝 y] w := by
          filter_upwards [isOpen_Iio.mem_nhds hyc] with z hz
          exact wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr (le_of_lt (mem_Iio.mp hz)))
        rw [hzw.deriv_eq]
        by_cases hy2 : c₀ / 2 ≤ y
        · exact le_trans (hL₁ y hy2 hyc) (le_max_left L₁ L₂)
        · have hmem : y ∈ Icc a_lo (c₀ / 2) := ⟨le_trans (min_le_left _ _) hy, le_of_lt (not_le.mp hy2)⟩
          have hL₂y : |deriv w y| ≤ L₂ := by simpa [Real.norm_eq_abs] using hL₂ y hmem
          exact (le_abs_self _).trans (hL₂y.trans (le_max_right L₁ L₂))
      · have hyc' : c₀ < y := lt_of_le_of_ne (not_lt.mp hyc) (Ne.symm hne)
        have heq : wExt w C =ᶠ[𝓝 y] fun z => w c₀ + (z - c₀) := by
          filter_upwards [isOpen_Ioi.mem_nhds hyc'] with z hz
          have hz' : ¬ z ≤ C.toReal := not_le.mpr (mem_Ioi.mp hz)
          simp [wExt, htop, hz', c₀]
        rw [heq.deriv_eq]
        have hd1 : HasDerivAt (fun z => w c₀ + (z - c₀)) (0 + 1) y :=
          (hasDerivAt_const y (w c₀)).add ((hasDerivAt_id y).sub_const c₀)
        rw [zero_add] at hd1
        rw [hd1.deriv]
        exact hL₀_ge1
    have hlip_all : ∀ {p q' : ℝ}, r₀ ≤ p → p ≤ q' → wExt w C q' - wExt w C p ≤ L₀ * (q' - p) := by
      intro p q' hp hpq
      by_cases hq2 : q' ≤ c₀ / 2
      · rcases eq_or_lt_of_le hpq with rfl | hlt
        · simp
        · rw [wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr (by linarith)),
              wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr (by linarith))]
          have hcont_seg : ContinuousOn w (Icc p q') := hw_cont.mono (fun z hz => show 0 ≤ z by linarith [hz.1, hp, hr₀])
          have hdiff_seg : DifferentiableOn ℝ w (Ioo p q') :=
            (hw_smooth.differentiableOn one_ne_zero).mono (fun z hz =>
              hsub_lo ⟨le_trans (min_le_left _ _) (le_trans hp (le_of_lt hz.1)), le_trans (le_of_lt hz.2) hq2⟩)
          obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope w hlt hcont_seg hdiff_seg
          have hξ_le : deriv w ξ ≤ L₀ := by
            have hmem : ξ ∈ Icc a_lo (c₀ / 2) :=
              ⟨le_trans (min_le_left _ _) (le_trans hp (le_of_lt hξ.1)), le_trans (le_of_lt hξ.2) hq2⟩
            have hL₂ξ : |deriv w ξ| ≤ L₂ := by simpa [Real.norm_eq_abs] using hL₂ ξ hmem
            exact (le_abs_self _).trans (hL₂ξ.trans (le_max_right L₁ L₂))
          rw [hslope, div_le_iff₀ (sub_pos.mpr hlt)] at hξ_le
          exact hξ_le
      · by_cases hp2 : c₀ / 2 ≤ p
        · exact wExt_lipschitz_above_half_C hC htop hw_cont hw_smooth hL₀_ge1
            (fun y hy1 hy2 => le_trans (hL₁ y hy1 hy2) (le_max_left L₁ L₂)) hp2 hpq
        · push Not at hq2 hp2
          have h1 : wExt w C (c₀ / 2) - wExt w C p ≤ L₀ * (c₀ / 2 - p) := by
            rw [wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr (by linarith)),
                wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr (by linarith))]
            have hcont_seg : ContinuousOn w (Icc p (c₀ / 2)) := hw_cont.mono (fun z hz => show 0 ≤ z by linarith [hz.1, hp, hr₀])
            have hdiff_seg : DifferentiableOn ℝ w (Ioo p (c₀ / 2)) :=
              (hw_smooth.differentiableOn one_ne_zero).mono (fun z hz =>
                hsub_lo ⟨le_trans (min_le_left _ _) (le_trans hp (le_of_lt hz.1)), le_of_lt hz.2⟩)
            obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope w hp2 hcont_seg hdiff_seg
            have hξ_le : deriv w ξ ≤ L₀ := by
              have hmem : ξ ∈ Icc a_lo (c₀ / 2) :=
                ⟨le_trans (min_le_left _ _) (le_trans hp (le_of_lt hξ.1)), le_of_lt hξ.2⟩
              have hL₂ξ : |deriv w ξ| ≤ L₂ := by simpa [Real.norm_eq_abs] using hL₂ ξ hmem
              exact (le_abs_self _).trans (hL₂ξ.trans (le_max_right L₁ L₂))
            rw [hslope, div_le_iff₀ (sub_pos.mpr hp2)] at hξ_le
            exact hξ_le
          have h2 : wExt w C q' - wExt w C (c₀ / 2) ≤ L₀ * (q' - c₀ / 2) :=
            wExt_lipschitz_above_half_C hC htop hw_cont hw_smooth hL₀_ge1
              (fun y hy1 hy2 => le_trans (hL₁ y hy1 hy2) (le_max_left L₁ L₂)) le_rfl (le_of_lt hq2)
          linarith
    refine ⟨L₀, hL₀_ge1, fun y hy hne => hderiv_le y (le_of_lt hy.1) (hne htop), ?_⟩
    intro u v hu huv
    have hdiff_le : min v M_cut - min u M_cut ≤ v - u := by
      cases le_total v M_cut with
      | inl hvM => rw [min_eq_left hvM, min_eq_left (le_trans huv hvM)]
      | inr hvM =>
        rw [min_eq_right hvM]
        cases le_total u M_cut with
        | inl huM => rw [min_eq_left huM]; linarith
        | inr huM => rw [min_eq_right huM]; linarith
    calc wExt w C (min v M_cut) - wExt w C (min u M_cut)
        ≤ L₀ * (min v M_cut - min u M_cut) := hlip_all (le_min hu hM) (min_le_min_right M_cut huv)
      _ ≤ L₀ * (v - u) := mul_le_mul_of_nonneg_left hdiff_le (by linarith)

private lemma wExt_ftc_on_Ioo {w : ℝ → ℝ} {C : ℝ≥0∞}
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    {r₀ M_cut L₀ : ℝ} (hr₀ : 0 < r₀) (_hL₀_ge1 : 1 ≤ L₀)
    (hL₀ : ∀ y ∈ Ioo r₀ M_cut, (C ≠ ⊤ → y ≠ C.toReal) → deriv (wExt w C) y ≤ L₀)
    {a b : ℝ} (ha : r₀ ≤ a) (hab : a ≤ b) (hb : b < M_cut) :
    IntegrableOn (deriv (wExt w C)) (Ioo a b) volume ∧
      ∫ y in Ioo a b, deriv (wExt w C) y = wExt w C b - wExt w C a := by
  have hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    isOpen_Ioi.inter (isOpen_lt ENNReal.continuous_ofReal continuous_const)
  have hderiv_cont : ContinuousOn (deriv w) {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.continuousOn_deriv_of_isOpen hopen le_rfl
  have hseg_below : ∀ {u v : ℝ}, r₀ ≤ u → u ≤ v → v < M_cut → ENNReal.ofReal v ≤ C →
      IntegrableOn (deriv (wExt w C)) (Ioo u v) volume ∧
        ∫ y in Ioo u v, deriv (wExt w C) y = wExt w C v - wExt w C u := by
    intro u v hu huv hvM hvC
    rcases eq_or_lt_of_le huv with rfl | hlt
    · simp
    · have hu_pos : 0 < u := lt_of_lt_of_le hr₀ hu
      have hsub_oo : Ioo u v ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := fun y hy =>
        ⟨lt_trans hu_pos hy.1, lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (lt_trans hu_pos hlt)).mpr hy.2) hvC⟩
      have hderiv_eq : EqOn (deriv (wExt w C)) (deriv w) (Ioo u v) := by
        intro y hy
        have hy_open : IsOpen {z : ℝ | ENNReal.ofReal z < ENNReal.ofReal v} :=
          isOpen_lt ENNReal.continuous_ofReal continuous_const
        have hzw : wExt w C =ᶠ[𝓝 y] w := by
          filter_upwards [hy_open.mem_nhds ((ENNReal.ofReal_lt_ofReal_iff (lt_trans hu_pos hlt)).mpr hy.2)] with z hz
          exact wExt_eq_of_le (le_trans (le_of_lt hz) hvC)
        exact hzw.deriv_eq
      have hint_w : IntegrableOn (deriv w) (Ioo u v) volume := by
        refine (integrableOn_const_of_lt_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) L₀).mono'
          ((hderiv_cont.mono hsub_oo).aestronglyMeasurable measurableSet_Ioo) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
        have h1 : 1 ≤ deriv w y := hw_grad y (hsub_oo hy).1 (hsub_oo hy).2
        have h2 : deriv w y ≤ L₀ := by
          rw [← hderiv_eq hy]
          exact hL₀ y ⟨lt_of_le_of_lt hu hy.1, lt_trans hy.2 hvM⟩ (fun htop => by
            have hlt_c : y < C.toReal := (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt (hsub_oo hy).1) htop).mp (hsub_oo hy).2
            exact ne_of_lt hlt_c)
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        exact h2
      have hint_ext : IntegrableOn (deriv (wExt w C)) (Ioo u v) volume :=
        (integrableOn_congr_fun hderiv_eq measurableSet_Ioo).mpr hint_w
      refine ⟨hint_ext, ?_⟩
      rw [setIntegral_congr_fun measurableSet_Ioo hderiv_eq,
          wExt_eq_of_le hvC,
          wExt_eq_of_le (le_trans (ENNReal.ofReal_le_ofReal (le_of_lt hlt)) hvC)]
      let vn : ℕ → ℝ := fun n => max u (v - 1 / (n + 1 : ℝ))
      have hvn_tend : Tendsto vn atTop (𝓝 v) := by
        have h1 : Tendsto (fun n : ℕ => v - 1 / (n + 1 : ℝ)) atTop (𝓝 (v - 0)) :=
          tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
        rw [sub_zero] at h1
        have h2 : Tendsto vn atTop (𝓝 (max u v)) := tendsto_const_nhds.max h1
        rwa [max_eq_right (le_of_lt hlt)] at h2
      have hvn_step : ∀ n : ℕ, ∫ y in Ioo u (vn n), deriv w y = w (vn n) - w u := by
        intro n
        have huvn : u ≤ vn n := le_max_left _ _
        rcases eq_or_lt_of_le huvn with heq | hlt_n
        · rw [← heq]; simp
        · have hv_lt : vn n < v := max_lt hlt (by linarith [show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity])
          have hsub_n : Icc u (vn n) ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := fun y hy =>
            ⟨lt_of_lt_of_le hu_pos hy.1,
             lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (lt_trans hu_pos hlt)).mpr (lt_of_le_of_lt hy.2 hv_lt)) hvC⟩
          have hcont_w : ContinuousOn w (Icc u (vn n)) := hw_cont.mono (fun y hy => le_trans (le_of_lt hu_pos) hy.1)
          have hhas_deriv : ∀ y ∈ Ioo u (vn n), HasDerivAt w (deriv w y) y := fun y hy =>
            ((hw_smooth.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds (hsub_n ⟨le_of_lt hy.1, le_of_lt hy.2⟩))).hasDerivAt
          have hint_ivl : IntervalIntegrable (deriv w) volume u (vn n) :=
            (intervalIntegrable_iff_integrableOn_Ioc_of_le huvn).mpr
              ((hderiv_cont.mono hsub_n).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
          rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le huvn]
          exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huvn hcont_w hhas_deriv hint_ivl
      have hLHS_tend : Tendsto (fun n => ∫ y in Ioo u (vn n), deriv w y) atTop (𝓝 (∫ y in Ioo u v, deriv w y)) := by
        have hrew : ∀ n, (∫ y in Ioo u (vn n), deriv w y) =
            ∫ y in Ioo u v, (Ioo u (vn n)).indicator (deriv w) y := by
          intro n
          rw [setIntegral_indicator measurableSet_Ioo]
          have hsub_inter : Ioo u v ∩ Ioo u (vn n) = Ioo u (vn n) :=
            inter_eq_right.mpr (fun y hy => ⟨hy.1, lt_of_lt_of_le hy.2 (max_le (le_of_lt hlt) (by linarith [show (0 : ℝ) ≤ 1 / (n + 1 : ℝ) by positivity]))⟩)
          rw [hsub_inter]
        simp_rw [hrew]
        apply tendsto_integral_of_dominated_convergence (fun y => |deriv w y|)
        · intro n; exact ((hderiv_cont.mono hsub_oo).aestronglyMeasurable measurableSet_Ioo).indicator measurableSet_Ioo
        · exact hint_w.norm
        · intro n; filter_upwards with y
          by_cases h : y ∈ Ioo u (vn n)
          · rw [Set.indicator_of_mem h, Real.norm_eq_abs]
          · rw [Set.indicator_of_notMem h, norm_zero]; exact abs_nonneg _
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
          obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.mpr hy.2)
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [eventually_ge_atTop N] with n hn
          have h1 : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) :=
            one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
          have hmem : y ∈ Ioo u (vn n) := ⟨hy.1, lt_of_lt_of_le (by linarith) (le_max_right _ _)⟩
          exact (Set.indicator_of_mem hmem _).symm
      have hRHS_tend : Tendsto (fun n => w (vn n) - w u) atTop (𝓝 (w v - w u)) := by
        have hcont_v : ContinuousWithinAt w (Ici 0) v := hw_cont v (le_of_lt (lt_trans hu_pos hlt))
        rw [ContinuousWithinAt] at hcont_v
        have h1 : Tendsto (w ∘ vn) atTop (𝓝 (w v)) := hcont_v.comp (by
          rw [nhdsWithin]; exact tendsto_inf.mpr ⟨hvn_tend, tendsto_principal.mpr (Eventually.of_forall fun n => le_trans (le_of_lt hu_pos) (le_max_left _ _))⟩)
        exact h1.sub tendsto_const_nhds
      exact tendsto_nhds_unique hLHS_tend (by simp_rw [hvn_step]; exact hRHS_tend)
  by_cases htop : C = ⊤
  · exact hseg_below ha hab hb (by rw [htop]; exact le_top)
  · set c₀ := C.toReal
    have hseg_above : ∀ {u v : ℝ}, c₀ ≤ u → u ≤ v →
        IntegrableOn (deriv (wExt w C)) (Ioo u v) volume ∧
          ∫ y in Ioo u v, deriv (wExt w C) y = wExt w C v - wExt w C u := by
      intro u v hu huv
      have hderiv_one : EqOn (deriv (wExt w C)) (fun _ => (1 : ℝ)) (Ioo u v) := by
        intro y hy
        have hyc : c₀ < y := lt_of_le_of_lt hu hy.1
        have heq : wExt w C =ᶠ[𝓝 y] fun z => w c₀ + (z - c₀) := by
          filter_upwards [isOpen_Ioi.mem_nhds hyc] with z hz
          have hz' : ¬ z ≤ C.toReal := not_le.mpr (mem_Ioi.mp hz)
          simp [wExt, htop, hz', c₀]
        rw [heq.deriv_eq]
        have hd1 : HasDerivAt (fun z => w c₀ + (z - c₀)) (0 + 1) y :=
          (hasDerivAt_const y (w c₀)).add ((hasDerivAt_id y).sub_const c₀)
        rw [zero_add] at hd1
        exact hd1.deriv
      have hint1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo u v) volume :=
        integrableOn_const_of_lt_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) 1
      refine ⟨(integrableOn_congr_fun hderiv_one measurableSet_Ioo).mpr hint1, ?_⟩
      rw [setIntegral_congr_fun measurableSet_Ioo hderiv_one, setIntegral_const, smul_eq_mul,
          mul_one, Measure.real_def, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr huv)]
      rcases eq_or_lt_of_le huv with rfl | hlt
      · simp
      · have hv_gt : ¬ v ≤ C.toReal := not_le.mpr (lt_of_le_of_lt hu hlt)
        by_cases hu_eq : u = C.toReal
        · subst hu_eq
          unfold wExt
          rw [if_neg htop, if_neg hv_gt, if_neg htop, if_pos le_rfl]
          ring
        · have hu_gt : ¬ u ≤ C.toReal := not_le.mpr (lt_of_le_of_ne hu (Ne.symm hu_eq))
          unfold wExt
          rw [if_neg htop, if_neg hv_gt, if_neg htop, if_neg hu_gt]
          ring
    by_cases hb_le : b ≤ c₀
    · exact hseg_below ha hab hb ((ENNReal.ofReal_le_iff_le_toReal htop).mpr hb_le)
    · by_cases ha_ge : c₀ ≤ a
      · exact hseg_above ha_ge hab
      · push Not at hb_le ha_ge
        have ⟨hi1, he1⟩ := hseg_below ha (le_of_lt ha_ge) (lt_trans hb_le hb)
          ((ENNReal.ofReal_le_iff_le_toReal htop).mpr le_rfl)
        have ⟨hi2, he2⟩ := hseg_above le_rfl (le_of_lt hb_le)
        have hunion_ae : (Ioo a c₀ ∪ Ioo c₀ b : Set ℝ) =ᵐ[volume] Ioo a b := by
          have hsub : Ioo a c₀ ∪ {c₀} ∪ Ioo c₀ b = Ioo a b := by
            ext y; simp only [mem_union, mem_Ioo, mem_singleton_iff]
            constructor
            · rintro ((⟨h1, h2⟩ | rfl) | ⟨h1, h2⟩)
              · exact ⟨h1, lt_trans h2 hb_le⟩
              · exact ⟨ha_ge, hb_le⟩
              · exact ⟨lt_trans ha_ge h1, h2⟩
            · rintro ⟨h1, h2⟩
              rcases lt_trichotomy y c₀ with hlt | rfl | hgt
              · exact Or.inl (Or.inl ⟨h1, hlt⟩)
              · exact Or.inl (Or.inr rfl)
              · exact Or.inr ⟨hgt, h2⟩
          rw [← hsub]
          have h1 : (Ioo a c₀ ∪ {c₀} : Set ℝ) =ᵐ[volume] Ioo a c₀ :=
            union_ae_eq_left_of_ae_eq_empty (by rw [ae_eq_empty]; simp)
          exact (h1.union EventuallyEq.rfl).symm
        have hdisj : Disjoint (Ioo a c₀) (Ioo c₀ b) := by
          rw [Set.disjoint_left]; intro y hy1 hy2; linarith [hy1.2, hy2.1]
        have hi12 : IntegrableOn (deriv (wExt w C)) (Ioo a c₀ ∪ Ioo c₀ b) volume := hi1.union hi2
        refine ⟨hi12.congr_set_ae hunion_ae.symm, ?_⟩
        rw [← setIntegral_congr_set hunion_ae, setIntegral_union hdisj measurableSet_Ioo hi1 hi2, he1, he2]
        ring

private lemma wExt_differentiableAt {w : ℝ → ℝ} {C : ℝ≥0∞}
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    {u : ℝ} (hu : 0 < u) (hne : C ≠ ⊤ → u ≠ C.toReal) :
    DifferentiableAt ℝ (wExt w C) u := by
  have hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    isOpen_Ioi.inter (isOpen_lt ENNReal.continuous_ofReal continuous_const)
  by_cases htop : C = ⊤
  · have hwext : wExt w C = w := by ext z; simp [wExt, htop]
    rw [hwext]
    exact (hw_smooth.differentiableOn one_ne_zero).differentiableAt
      (hopen.mem_nhds ⟨hu, by rw [htop]; exact ENNReal.ofReal_lt_top⟩)
  · rcases lt_or_gt_of_ne (hne htop) with hlt_c | hgt_c
    · have hzw : wExt w C =ᶠ[𝓝 u] w := by
        filter_upwards [isOpen_Iio.mem_nhds hlt_c] with z hz
        exact wExt_eq_of_le ((ENNReal.ofReal_le_iff_le_toReal htop).mpr (le_of_lt (mem_Iio.mp hz)))
      exact ((hw_smooth.differentiableOn one_ne_zero).differentiableAt
        (hopen.mem_nhds ⟨hu, (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hu) htop).mpr hlt_c⟩)).congr_of_eventuallyEq hzw
    · have hzw : wExt w C =ᶠ[𝓝 u] fun z => w C.toReal + (z - C.toReal) := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt_c] with z hz
        have hz' : ¬ z ≤ C.toReal := not_le.mpr (mem_Ioi.mp hz)
        simp [wExt, htop, hz']
      exact (((hasDerivAt_const _ _).add ((hasDerivAt_id _).sub_const _)).differentiableAt).congr_of_eventuallyEq hzw

private lemma exists_smooth_supersolution (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) {q : ℝ} (hq : 0 < q)
    {w : ℝ → ℝ} {C : ℝ≥0∞} (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    {x Z_max T ε : ℝ} (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (hxZ : x ≤ Z_max) (hZC : C ≠ ⊤ → Z_max ≤ C.toReal) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ (F : ℝ → ℝ) (B₀ a : ℝ),
      0 < a ∧ (∀ y < -a, F y = 0) ∧
      0 ≤ B₀ ∧ Monotone F ∧ (∀ y, 0 ≤ F y) ∧ (∀ y, F y ≤ B₀) ∧
      Differentiable ℝ F ∧ Continuous (deriv F) ∧
      (∀ u v, 0 ≤ u → u ≤ v → v ≤ Z_max + X.drift * T + 1 → v - u ≤ F v - F u) ∧
      F x ≤ w x + ε ∧
      (∀ z ∈ Icc (0 : ℝ) Z_max,
        IntegrableOn (fun u => F (z + u) - F z) (Iio (0 : ℝ)) X.ν ∧
        X.drift * deriv F z + ∫ u in Iio (0 : ℝ), (F (z + u) - F z) ∂X.ν - q * F z ≤ ε) := by
  have hd : 0 < X.drift := drift_pos X hX hBV
  have hZ0 : 0 ≤ Z_max := le_trans hx hxZ
  have hdT_nn : 0 ≤ X.drift * T := mul_nonneg (le_of_lt hd) hT
  set M := Z_max + X.drift * T + 1
  have hM_def : M = Z_max + X.drift * T + 1 := rfl
  have hM_pos : 1 ≤ M := by linarith
  set M_cut := M + 1
  have hM_cut_def : M_cut = M + 1 := rfl
  obtain ⟨η, hη_nn, hη_tend, hη_gen⟩ :=
    exists_wExt_gen_error X hX hBV hq hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
  have hη_ev : ∀ᶠ u in 𝓝[>] (0 : ℝ), η u < ε := (tendsto_order.mp hη_tend).2 ε hε
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hη_ev
  obtain ⟨r₁, hr₁_pos, hr₁⟩ := hη_ev
  have hwext_cont_x : ContinuousWithinAt (wExt w C) (Ici 0) x := wExt_continuousOn hw_cont x hx
  rw [Metric.continuousWithinAt_iff] at hwext_cont_x
  obtain ⟨r₂, hr₂_pos, hr₂⟩ := hwext_cont_x ε hε
  set r_cap : ℝ := if htop : C = ⊤ then 1 else C.toReal / 8
  have hr_cap_pos : 0 < r_cap := by
    dsimp [r_cap]; split_ifs with htop
    · norm_num
    · have hc₀ : 0 < C.toReal := ENNReal.toReal_pos (ne_of_gt hC) htop
      linarith
  set r' := min (min (r₁ / 2) (r₂ / 2)) (min (1 / 4) (r_cap / 2))
  have hr'_pos : 0 < r' := lt_min (lt_min (half_pos hr₁_pos) (half_pos hr₂_pos))
    (lt_min (by norm_num) (half_pos hr_cap_pos))
  have hr'_lt1 : r' < r₁ := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (half_lt_self hr₁_pos)
  have hr'_lt2 : r' < r₂ := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (half_lt_self hr₂_pos)
  have hr'_lt_q : r' < 1 / 2 := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by norm_num)
  have hr'_lt_cap : C ≠ ⊤ → r' < C.toReal / 8 := by
    intro htop
    have h1 : r' ≤ r_cap / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : r_cap = C.toReal / 8 := dif_neg htop
    linarith [hr_cap_pos]
  set r := 4 * r' / 5
  set δ := r' / 10
  have hr_def : r = 4 * r' / 5 := rfl
  have hδ_def : δ = r' / 10 := rfl
  have hr_pos : 0 < r := by positivity
  have hδ_pos : 0 < δ := by positivity
  have hr2δ : r + 2 * δ = r' := by dsimp [r, δ]; ring
  have hη_le : η r' ≤ ε := le_of_lt (hr₁
    (by rw [Real.dist_eq, sub_zero, abs_of_pos hr'_pos]; exact hr'_lt1)
    (mem_Ioi.mpr hr'_pos))
  have hmono_ext := wExt_mono hw_cont hw0 hw_neg hw_smooth hw_grad
  have hnn_ext := wExt_nonneg hw_cont hw0 hw_neg hw_smooth hw_grad
  set B₀ := wExt w C M_cut
  have hB₀_nn : 0 ≤ B₀ := hnn_ext M_cut
  obtain ⟨L₀, hL₀_ge1, hL₀_deriv, hL₀_lip⟩ :=
    wExt_lipschitz_above_pos X hX hBV hq hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      (r₀ := r / 2) (M_cut := M_cut) (half_pos hr_pos) (by linarith)
  let g₀ : ℝ → ℝ := fun y => wExt w C (min (y + r) M_cut)
  have hg₀_mono : Monotone g₀ := fun u v huv =>
    hmono_ext (min_le_min_right M_cut (by linarith))
  have hg₀_nn : ∀ y, 0 ≤ g₀ y := fun y => hnn_ext _
  have hg₀_bdd : ∀ y, g₀ y ≤ B₀ := fun y => hmono_ext (min_le_right _ _)
  have hg₀_cont : ContinuousOn g₀ (Ici (-r)) := by
    have hinner_cont : Continuous (fun y : ℝ => min (y + r) M_cut) :=
      (continuous_id.add continuous_const).min continuous_const
    exact (wExt_continuousOn hw_cont).comp hinner_cont.continuousOn
      (fun y hy => show 0 ≤ min (y + r) M_cut from le_min (by linarith [mem_Ici.mp hy]) (by linarith))
  have hg₀_lip : ∀ u v, -r / 2 ≤ u → u ≤ v → g₀ v - g₀ u ≤ L₀ * (v - u) := by
    intro u v hu huv
    have h1 := hL₀_lip (u + r) (v + r) (by linarith) (by linarith)
    simpa [g₀] using h1
  have hg₀_ftc : ∀ z ∈ Icc (0 : ℝ) (Z_max + δ),
      IntegrableOn (fun s => deriv g₀ (z + s)) (Ioo (0 : ℝ) δ) volume ∧
      ∫ s in Ioo (0 : ℝ) δ, deriv g₀ (z + s) = g₀ (z + δ) - g₀ z := by
    intro z hz
    have h_lt_M : z + δ + r < M_cut := by linarith [hz.2]
    have hderiv_ae : (fun s => deriv g₀ (z + s)) =ᵐ[volume.restrict (Ioo (0 : ℝ) δ)]
        (fun s => deriv (wExt w C) (z + r + s)) := by
      have hae_ne : ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) δ)), (C ≠ ⊤ → s ≠ C.toReal - z - r) := by
        by_cases htop : C = ⊤
        · exact ae_of_all _ (fun _ h => absurd htop h)
        · rw [ae_iff]
          have : {s | ¬ (C ≠ ⊤ → s ≠ C.toReal - z - r)} = {C.toReal - z - r} := by
            ext s; simp [htop]
          rw [this, Measure.restrict_apply (measurableSet_singleton _)]
          exact measure_mono_null inter_subset_left Real.volume_singleton
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hae_ne] with s hs hne
      have hs_lt : z + s + r < M_cut := by linarith [hs.2]
      have heq_loc : g₀ =ᶠ[𝓝 (z + s)] fun y => wExt w C (y + r) := by
        filter_upwards [(isOpen_lt (continuous_id.add continuous_const) continuous_const).mem_nhds hs_lt] with y hy
        dsimp only [g₀]
        exact congrArg (wExt w C) (min_eq_left (le_of_lt hy))
      rw [heq_loc.deriv_eq]
      have hdiff_at : DifferentiableAt ℝ (wExt w C) ((z + s) + r) :=
        wExt_differentiableAt hw_smooth (by linarith [hz.1, hs.1])
          (fun htop hc => hne htop (by linarith))
      exact (hdiff_at.hasDerivAt.comp (z + s) ((hasDerivAt_id (z + s)).add_const r)).deriv.trans
        ((mul_one _).trans (congrArg (deriv (wExt w C)) (by ring : z + s + r = z + r + s)))
    have hftc_ext := wExt_ftc_on_Ioo hw_cont hw_smooth hw_grad (half_pos hr_pos) hL₀_ge1 hL₀_deriv
      (a := z + r) (b := z + r + δ) (by linarith [hz.1]) (by linarith) (by linarith)
    have hshift_int : IntegrableOn (fun s => deriv (wExt w C) (z + r + s)) (Ioo (0 : ℝ) δ) volume ∧
        ∫ s in Ioo (0 : ℝ) δ, deriv (wExt w C) (z + r + s) = ∫ y in Ioo (z + r) (z + r + δ), deriv (wExt w C) y := by
      have hpre : (fun s => z + r + s) ⁻¹' Ioo (z + r) (z + r + δ) = Ioo (0 : ℝ) δ := by
        ext s; simp only [mem_preimage, mem_Ioo]
        constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
      have hmp : MeasurePreserving (fun s : ℝ => z + r + s) volume volume :=
        measurePreserving_add_left volume (z + r)
      have hemb : MeasurableEmbedding (fun s : ℝ => z + r + s) := measurableEmbedding_addLeft (z + r)
      constructor
      · rw [← hpre]
        exact (hmp.integrableOn_comp_preimage hemb).mpr hftc_ext.1
      · rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hδ_pos.le,
            intervalIntegral.integral_comp_add_left, add_zero,
            intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine ⟨(integrable_congr hderiv_ae.symm).mp hshift_int.1, ?_⟩
    rw [integral_congr_ae hderiv_ae, hshift_int.2, hftc_ext.2]
    dsimp [g₀]
    rw [min_eq_left (by linarith : z + δ + r ≤ M_cut), min_eq_left (by linarith : z + r ≤ M_cut)]
    ring_nf
  have hg₀_gen : ∀ y ∈ Ioo (0 : ℝ) (Z_max + δ + δ), y ≠ C.toReal - r →
      IntegrableOn (fun u => g₀ (y + u) - g₀ y) (Iio (0 : ℝ)) X.ν ∧
      X.drift * deriv g₀ y + ∫ u in Iio (0 : ℝ), (g₀ (y + u) - g₀ y) ∂X.ν - q * g₀ y ≤ ε := by
    intro y hy hne
    have hyr_lt : y + r < M_cut := by linarith [hy.2]
    have heq_loc : g₀ =ᶠ[𝓝 y] fun z => wExt w C (z + r) := by
      filter_upwards [(isOpen_lt (continuous_id.add continuous_const) continuous_const).mem_nhds hyr_lt] with z hz
      dsimp only [g₀]
      exact congrArg (wExt w C) (min_eq_left (le_of_lt hz))
    have hdiff_at : DifferentiableAt ℝ (wExt w C) (y + r) :=
      wExt_differentiableAt hw_smooth (by linarith [hy.1]) (fun _ hc => hne (by linarith))
    have hderiv_g₀ : deriv g₀ y = deriv (wExt w C) (y + r) := by
      rw [heq_loc.deriv_eq]
      exact (hdiff_at.hasDerivAt.comp y ((hasDerivAt_id y).add_const r)).deriv.trans (mul_one _)
    have hfun_eq : EqOn (fun u => g₀ (y + u) - g₀ y) (fun u => wExt w C (y + r + u) - wExt w C (y + r)) (Iio (0 : ℝ)) := by
      intro u hu
      dsimp [g₀]
      rw [min_eq_left (by linarith [mem_Iio.mp hu] : y + u + r ≤ M_cut),
          min_eq_left (le_of_lt hyr_lt)]
      ring_nf
    have hgy_eq : g₀ y = wExt w C (y + r) := by
      dsimp only [g₀]; exact congrArg (wExt w C) (min_eq_left (le_of_lt hyr_lt))
    have hgen_ext := hη_gen r' hr'_pos hr'_lt_cap (y + r) (by linarith [hy.1])
      (by by_cases htop : C = ⊤
          · exact Or.inl htop
          · exact Or.inr (by linarith [hy.2, hZC htop]))
      (fun _ hc => hne (by linarith))
    refine ⟨(integrableOn_congr_fun hfun_eq measurableSet_Iio).mpr hgen_ext.1, ?_⟩
    rw [hderiv_g₀, setIntegral_congr_fun measurableSet_Iio hfun_eq, hgy_eq]
    linarith [hgen_ext.2]
  have hstep1 := steklov_step X hBV hδ_pos hr_pos (by linarith : r / 2 < 1) (by linarith : 0 ≤ Z_max + δ)
    (by linarith : 0 ≤ L₀) hg₀_mono hg₀_nn hg₀_bdd hg₀_cont hg₀_lip hg₀_ftc hg₀_gen
  set W1 := steklov δ g₀
  rcases hstep1 with ⟨hW1_mono, hW1_nn, hW1_bdd, hW1_cont, hW1_lip, hW1_gen⟩
  have hW1_ftc : ∀ z ∈ Icc (0 : ℝ) Z_max,
      IntegrableOn (fun s => deriv W1 (z + s)) (Ioo (0 : ℝ) δ) volume ∧
      ∫ s in Ioo (0 : ℝ) δ, deriv W1 (z + s) = W1 (z + δ) - W1 z := by
    intro z hz
    have hhas_s : ∀ s ∈ Icc (0 : ℝ) δ, HasDerivAt (fun u => W1 (z + u)) ((g₀ (z + s + δ) - g₀ (z + s)) / δ) s := by
      intro s hs
      have h1 : HasDerivAt W1 ((g₀ (z + s + δ) - g₀ (z + s)) / δ) (z + s) :=
        steklov_hasDerivAt_of_continuousOn hδ_pos hg₀_cont (by linarith [hz.1, hs.1])
      have h2 := h1.comp s ((hasDerivAt_const s z).add (hasDerivAt_id s))
      rwa [zero_add, mul_one] at h2
    have hd_eq : EqOn (fun s => deriv W1 (z + s)) (fun s => (g₀ (z + s + δ) - g₀ (z + s)) / δ) (Icc (0 : ℝ) δ) := by
      intro s hs
      exact (steklov_hasDerivAt_of_continuousOn hδ_pos hg₀_cont (by linarith [hz.1, hs.1])).deriv
    have hcont_d : ContinuousOn (fun s => (g₀ (z + s + δ) - g₀ (z + s)) / δ) (Icc (0 : ℝ) δ) := by
      refine ((hg₀_cont.comp ((continuous_const.add continuous_id).add continuous_const).continuousOn
        (fun s hs => show -r ≤ z + s + δ by linarith [hz.1, hs.1])).sub
        (hg₀_cont.comp (continuous_const.add continuous_id).continuousOn
          (fun s hs => show -r ≤ z + s by linarith [hz.1, hs.1]))).div_const δ
    have hint_ivl : IntervalIntegrable (fun s => deriv W1 (z + s)) volume 0 δ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ_pos.le]
      exact (integrableOn_congr_fun (hd_eq.mono Ioc_subset_Icc_self) measurableSet_Ioc).mpr
        (hcont_d.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    constructor
    · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ_pos.le).mp hint_ivl).mono_set Ioo_subset_Ioc_self
    · rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hδ_pos.le]
      have hcont_shift : Continuous (fun u : ℝ => W1 (z + u)) :=
        hW1_cont.comp (continuous_const.add continuous_id)
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (f := fun u => W1 (z + u)) (f' := fun s => deriv W1 (z + s)) hδ_pos.le
        hcont_shift.continuousOn
        (fun s hs => by
          have hd_val : deriv W1 (z + s) = (g₀ (z + s + δ) - g₀ (z + s)) / δ :=
            hd_eq ⟨le_of_lt hs.1, le_of_lt hs.2⟩
          rw [hd_val]
          exact hhas_s s ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
        hint_ivl
      rwa [add_zero] at hftc
  have hstep2 := steklov_step X hBV (y_bad := 0) hδ_pos (half_pos hr_pos) (by linarith : (r / 2) / 2 < 1) hZ0
    (by linarith : 0 ≤ L₀) hW1_mono hW1_nn hW1_bdd hW1_cont.continuousOn
    (fun u v hu huv => hW1_lip u v (by linarith) huv) hW1_ftc
    (fun y hy _ => hW1_gen y ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
  set F := steklov δ W1
  rcases hstep2 with ⟨hF_mono, hF_nn, hF_bdd, _, _, hF_gen⟩
  have hF_hasDeriv : ∀ y, HasDerivAt F ((W1 (y + δ) - W1 y) / δ) y :=
    steklov_hasDerivAt_global hδ_pos hW1_cont
  have hF_diff : Differentiable ℝ F := fun y => (hF_hasDeriv y).differentiableAt
  have hF_deriv_eq : deriv F = fun y => (W1 (y + δ) - W1 y) / δ := by
    ext y; exact (hF_hasDeriv y).deriv
  have hF_deriv_cont : Continuous (deriv F) := by
    rw [hF_deriv_eq]
    exact ((hW1_cont.comp (continuous_id.add continuous_const)).sub hW1_cont).div_const δ
  refine ⟨F, B₀, r', hr'_pos, ?_, hB₀_nn, hF_mono, hF_nn, hF_bdd, hF_diff, hF_deriv_cont, ?_, ?_, hF_gen⟩
  · intro y hy
    have hW1_zero : ∀ z ≤ -r - δ, W1 z = 0 := by
      intro z hz
      simp only [W1, steklov_eq_setIntegral hδ_pos]
      have h0 : EqOn (fun s => g₀ (z + s)) 0 (Ioo (0 : ℝ) δ) := by
        intro s hs
        dsimp [g₀]
        have hneg : z + s + r < 0 := by linarith [hs.2]
        rw [min_eq_left (by linarith : z + s + r ≤ M_cut)]
        exact wExt_eq_zero_of_neg hw_neg hneg
      rw [setIntegral_congr_fun measurableSet_Ioo h0]; simp
    simp only [F, steklov_eq_setIntegral hδ_pos]
    have h0 : EqOn (fun s => W1 (y + s)) 0 (Ioo (0 : ℝ) δ) := by
      intro s hs
      exact hW1_zero (y + s) (by linarith [hs.2])
    rw [setIntegral_congr_fun measurableSet_Ioo h0]; simp
  · intro u v hu huv hvM
    rcases eq_or_lt_of_le huv with rfl | hlt
    · simp
    · obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope F hlt
        hF_diff.continuous.continuousOn hF_diff.differentiableOn
      have hderiv_ge1 : 1 ≤ deriv F ξ := by
        rw [hF_deriv_eq]
        dsimp only
        rw [le_div_iff₀ hδ_pos, one_mul]
        simp only [W1, steklov_eq_setIntegral hδ_pos]
        have hint1 := monotone_shift_integrableOn (δ := δ) hg₀_mono (ξ + δ)
        have hint2 := monotone_shift_integrableOn (δ := δ) hg₀_mono ξ
        rw [← mul_sub, ← integral_sub hint1 hint2]
        have hle_int : ∫ _ in Ioo (0 : ℝ) δ, δ ≤ ∫ s in Ioo (0 : ℝ) δ, (g₀ (ξ + δ + s) - g₀ (ξ + s)) := by
          apply setIntegral_mono_on
            (integrableOn_const_of_lt_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) δ)
            (hint1.sub hint2) measurableSet_Ioo
          intro s hs
          dsimp [g₀]
          rw [min_eq_left (by linarith [hξ.2, hs.2] : ξ + δ + s + r ≤ M_cut),
              min_eq_left (by linarith [hξ.2, hs.2] : ξ + s + r ≤ M_cut)]
          have hge := wExt_sub_ge_sub hw_cont hw_smooth hw_grad (a := ξ + s + r) (b := ξ + δ + s + r)
            (by linarith [hξ.1, hs.1]) (by linarith)
          linarith
        have hconst : ∫ _ in Ioo (0 : ℝ) δ, δ = δ * δ := by
          rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioo, sub_zero,
              ENNReal.toReal_ofReal hδ_pos.le]
        rw [hconst] at hle_int
        exact le_trans (by field_simp [hδ_pos.ne']; exact le_rfl : δ ≤ (1 / δ) * (δ * δ))
          (mul_le_mul_of_nonneg_left hle_int (by positivity))
      rw [hslope, le_div_iff₀ (sub_pos.mpr hlt)] at hderiv_ge1
      linarith
  · have hW1_le : ∀ z ∈ Icc x (x + δ), W1 z ≤ w x + ε := by
      intro z hz
      simp only [W1, steklov_eq_setIntegral hδ_pos]
      have hint_z := monotone_shift_integrableOn (δ := δ) hg₀_mono z
      have hle_int : ∫ s in Ioo (0 : ℝ) δ, g₀ (z + s) ≤ ∫ _ in Ioo (0 : ℝ) δ, (w x + ε) := by
        apply setIntegral_mono_on hint_z
          (integrableOn_const_of_lt_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) _)
          measurableSet_Ioo
        intro s hs
        dsimp [g₀]
        rw [min_eq_left (by linarith [hz.2, hs.2] : z + s + r ≤ M_cut)]
        have hdist : dist (z + s + r) x < r₂ := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith [hz.1, hs.1])]
          linarith [hz.2, hs.2]
        have hnear := hr₂ (show 0 ≤ z + s + r by linarith [hz.1, hs.1]) hdist
        rw [Real.dist_eq, wExt_eq_of_le hxc] at hnear
        linarith [(abs_lt.mp hnear).2]
      have hconst : ∫ _ in Ioo (0 : ℝ) δ, (w x + ε) = δ * (w x + ε) := by
        rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioo, sub_zero,
            ENNReal.toReal_ofReal hδ_pos.le]
      rw [hconst] at hle_int
      calc (1 / δ) * ∫ s in Ioo (0 : ℝ) δ, g₀ (z + s)
          ≤ (1 / δ) * (δ * (w x + ε)) := mul_le_mul_of_nonneg_left hle_int (by positivity)
        _ = w x + ε := by field_simp [hδ_pos.ne']
    simp only [F, steklov_eq_setIntegral hδ_pos]
    have hint_Fx := monotone_shift_integrableOn (δ := δ) hW1_mono x
    have hle_int : ∫ s in Ioo (0 : ℝ) δ, W1 (x + s) ≤ ∫ _ in Ioo (0 : ℝ) δ, (w x + ε) := by
      apply setIntegral_mono_on hint_Fx
        (integrableOn_const_of_lt_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) _)
        measurableSet_Ioo
      intro s hs; exact hW1_le (x + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hconst : ∫ _ in Ioo (0 : ℝ) δ, (w x + ε) = δ * (w x + ε) := by
      rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioo, sub_zero,
          ENNReal.toReal_ofReal hδ_pos.le]
    rw [hconst] at hle_int
    calc (1 / δ) * ∫ s in Ioo (0 : ℝ) δ, W1 (x + s)
        ≤ (1 / δ) * (δ * (w x + ε)) := mul_le_mul_of_nonneg_left hle_int (by positivity)
      _ = w x + ε := by field_simp [hδ_pos.ne']

/-! ### Section 4: Exponential sum approximation via Weierstrass -/

private lemma hasDerivAt_fin_sum {N : ℕ} {f : Fin N → ℝ → ℝ} {f' : Fin N → ℝ} {x : ℝ}
    (h : ∀ i : Fin N, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (fun y => ∑ i : Fin N, f i y) (∑ i : Fin N, f' i) x := by
  have h1 : HasDerivAt (∑ i ∈ Finset.univ, f i) (∑ i ∈ Finset.univ, f' i) x :=
    HasDerivAt.sum (fun i _ => h i)
  exact h1.congr_of_eventuallyEq (Eventually.of_forall fun y => (Finset.sum_apply y Finset.univ f).symm)

private lemma log_pullback_hasDerivAt {F : ℝ → ℝ} {a : ℝ} (_ha : 0 < a)
    (hF_zero : ∀ y < -a, F y = 0)
    (hF_diff : Differentiable ℝ F) (hF_deriv_cont : Continuous (deriv F)) :
    let H : ℝ → ℝ := fun t => if t ≤ 0 then 0 else F (Real.log t)
    let H' : ℝ → ℝ := fun t => if t ≤ 0 then 0 else deriv F (Real.log t) / t
    H 0 = 0 ∧ (∀ t : ℝ, HasDerivAt H (H' t) t) ∧ Continuous H' := by
  intro H H'
  have hderiv_zero : ∀ y < -a, deriv F y = 0 := by
    intro y hy
    have heq : F =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hy] with z hz
      exact hF_zero z (mem_Iio.mp hz)
    rw [heq.deriv_eq, deriv_const]
  have h_vanish : ∀ t < Real.exp (-a), H t = 0 ∧ H' t = 0 := by
    intro t ht
    by_cases ht0 : t ≤ 0
    · simp [H, H', ht0]
    · push Not at ht0
      have hlog : Real.log t < -a := by
        calc Real.log t < Real.log (Real.exp (-a)) := Real.log_lt_log ht0 ht
          _ = -a := Real.log_exp (-a)
      simp [H, H', not_le.mpr ht0, hF_zero _ hlog, hderiv_zero _ hlog]
  refine ⟨by simp [H], ?_, ?_⟩
  · intro t
    by_cases ht : 0 < t
    · have heq : H =ᶠ[𝓝 t] fun s => F (Real.log s) := by
        filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
        simp [H, not_le.mpr (mem_Ioi.mp hs)]
      have hd : HasDerivAt (fun s => F (Real.log s)) (deriv F (Real.log t) * t⁻¹) t :=
        (hF_diff (Real.log t)).hasDerivAt.comp t (Real.hasDerivAt_log (ne_of_gt ht))
      have hH't : H' t = deriv F (Real.log t) * t⁻¹ := by
        simp [H', not_le.mpr ht, div_eq_mul_inv]
      rw [hH't]
      exact hd.congr_of_eventuallyEq heq
    · have ht_lt : t < Real.exp (-a) := lt_of_le_of_lt (not_lt.mp ht) (Real.exp_pos (-a))
      have heq : H =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds ht_lt] with s hs
        exact (h_vanish s (mem_Iio.mp hs)).1
      rw [(h_vanish t ht_lt).2]
      exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq
  · rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : 0 < t
    · have heq : H' =ᶠ[𝓝 t] fun s => deriv F (Real.log s) / s := by
        filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
        simp [H', not_le.mpr (mem_Ioi.mp hs)]
      have hc : ContinuousAt (fun s => deriv F (Real.log s) / s) t :=
        (hF_deriv_cont.continuousAt.comp (Real.continuousAt_log (ne_of_gt ht))).div
          continuousAt_id (ne_of_gt ht)
      exact hc.congr_of_eventuallyEq heq
    · have ht_lt : t < Real.exp (-a) := lt_of_le_of_lt (not_lt.mp ht) (Real.exp_pos (-a))
      have heq : H' =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds ht_lt] with s hs
        exact (h_vanish s (mem_Iio.mp hs)).2
      exact (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq heq

private lemma exp_sum_gen_eq (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    {N : ℕ} (c : Fin N → ℝ) (z : ℝ) :
    let g : ℝ → ℝ := fun y => ∑ i : Fin N, c i * Real.exp (((i : ℕ) + 1 : ℝ) * y)
    IntegrableOn (fun u => g (z + u) - g z) (Iio (0 : ℝ)) X.ν ∧
      X.drift * deriv g z + ∫ u in Iio (0 : ℝ), (g (z + u) - g z) ∂X.ν =
        ∑ i : Fin N, c i * Real.exp (((i : ℕ) + 1 : ℝ) * z) * X.ψ ((i : ℕ) + 1 : ℝ) := by
  intro g
  have hterm_int : ∀ i : Fin N, IntegrableOn
      (fun u => c i * Real.exp (((i : ℕ) + 1 : ℝ) * z) * (Real.exp (((i : ℕ) + 1 : ℝ) * u) - 1))
      (Iio (0 : ℝ)) X.ν := fun i =>
    (nu_Iio_exp_sub_one_integrable X hBV (by positivity : 0 ≤ ((i : ℕ) + 1 : ℝ))).const_mul _
  have hdiff_eq : (fun u => g (z + u) - g z) = fun u =>
      ∑ i : Fin N, c i * Real.exp (((i : ℕ) + 1 : ℝ) * z) * (Real.exp (((i : ℕ) + 1 : ℝ) * u) - 1) := by
    ext u
    dsimp only [g]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_add, Real.exp_add]
    ring
  have hint : IntegrableOn (fun u => g (z + u) - g z) (Iio (0 : ℝ)) X.ν := by
    rw [hdiff_eq]
    exact integrable_finsetSum Finset.univ (fun i _ => hterm_int i)
  have hderiv_g : deriv g z = ∑ i : Fin N, c i * (((i : ℕ) + 1 : ℝ) * Real.exp (((i : ℕ) + 1 : ℝ) * z)) := by
    have hd : HasDerivAt g (∑ i : Fin N, c i * (Real.exp (((i : ℕ) + 1 : ℝ) * z) * (((i : ℕ) + 1 : ℝ) * 1))) z := by
      dsimp only [g]
      apply hasDerivAt_fin_sum
      intro i
      exact ((Real.hasDerivAt_exp _).comp z ((hasDerivAt_id z).const_mul _)).const_mul (c i)
    rw [hd.deriv]
    apply Finset.sum_congr rfl; intro i _; ring
  refine ⟨hint, ?_⟩
  rw [hderiv_g, hdiff_eq, integral_finsetSum Finset.univ (fun i _ => hterm_int i), Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, psi_eq_bv X hBV (by positivity : 0 ≤ ((i : ℕ) + 1 : ℝ))]
  ring

private lemma exists_exp_sum_approx (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    {F : ℝ → ℝ} {a Z_max M ε₁ : ℝ} (ha : 0 < a) (_hZ : 0 ≤ Z_max) (hZM : Z_max ≤ M) (hε₁ : 0 < ε₁)
    (hF_zero : ∀ y < -a, F y = 0)
    (hF_diff : Differentiable ℝ F) (hF_deriv_cont : Continuous (deriv F))
    (hF_int : ∀ z ∈ Icc (0 : ℝ) Z_max, IntegrableOn (fun u => F (z + u) - F z) (Iio (0 : ℝ)) X.ν) :
    ∃ (N : ℕ) (c : Fin N → ℝ),
      let g : ℝ → ℝ := fun y => ∑ i : Fin N, c i * Real.exp (((i : ℕ) + 1 : ℝ) * y)
      let Δ : ℝ → ℝ := fun y => F y - g y
      (∀ y ≤ M, |Δ y| ≤ ε₁) ∧
      (∀ u v, u ≤ v → v ≤ M → |Δ v - Δ u| ≤ ε₁ * (v - u)) ∧
      (∀ z ∈ Icc (0 : ℝ) Z_max,
        (∑ i : Fin N, c i * Real.exp (((i : ℕ) + 1 : ℝ) * z) * X.ψ ((i : ℕ) + 1 : ℝ)) -
          (X.drift * deriv F z + ∫ u in Iio (0 : ℝ), (F (z + u) - F z) ∂X.ν) ≤ ε₁) := by
  obtain ⟨hH0, hH_deriv, hH'_cont⟩ := log_pullback_hasDerivAt ha hF_zero hF_diff hF_deriv_cont
  set H : ℝ → ℝ := fun t => if t ≤ 0 then 0 else F (Real.log t)
  set H' : ℝ → ℝ := fun t => if t ≤ 0 then 0 else deriv F (Real.log t) / t
  set R := Real.exp M
  have hR_pos : 0 < R := Real.exp_pos M
  have hnu_1 : X.ν (Iic (-1 : ℝ)) < ⊤ := nu_Iic_neg_lt_top X zero_lt_one
  have hint_abs1 : 0 ≤ ∫ u in Ioo (-1 : ℝ) 0, |u| ∂X.ν := integral_nonneg fun u => abs_nonneg u
  set K_gen := |X.drift| + 2 * (X.ν (Iic (-1 : ℝ))).toReal + (∫ u in Ioo (-1 : ℝ) 0, |u| ∂X.ν) + 1
  have hK_gen_ge1 : 1 ≤ K_gen := by
    have : 0 ≤ 2 * (X.ν (Iic (-1 : ℝ))).toReal := by positivity
    linarith [abs_nonneg X.drift]
  set ε' := ε₁ / (max 1 R * K_gen)
  have hε'_pos : 0 < ε' := div_pos hε₁ (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left 1 R)) (by linarith))
  have hε'R_le_gen : (ε' * R) * K_gen ≤ ε₁ := by
    have hR_le : R ≤ max 1 R := le_max_right 1 R
    calc (ε' * R) * K_gen = ε' * (R * K_gen) := by ring
      _ ≤ ε' * (max 1 R * K_gen) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hR_le (by linarith)) (le_of_lt hε'_pos)
      _ = ε₁ := div_mul_cancel₀ ε₁ (ne_of_gt (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left 1 R)) (by linarith)))
  have hε'R_le : ε' * R ≤ ε₁ := by
    have : ε' * R * 1 ≤ (ε' * R) * K_gen := mul_le_mul_of_nonneg_left hK_gen_ge1 (by positivity)
    linarith
  let H'_map : C(Icc (0 : ℝ) R, ℝ) := ⟨fun t => H' t.1, hH'_cont.comp continuous_subtype_val⟩
  obtain ⟨Q, hQ⟩ := exists_polynomial_near_continuousMap 0 R H'_map ε' hε'_pos
  have hQ_pt : ∀ t ∈ Icc (0 : ℝ) R, |Q.eval t - H' t| ≤ ε' := by
    intro t ht
    have hle := ContinuousMap.norm_coe_le_norm (Q.toContinuousMapOn (Icc 0 R) - H'_map) ⟨t, ht⟩
    have hval : (Q.toContinuousMapOn (Icc 0 R) - H'_map) ⟨t, ht⟩ = Q.eval t - H' t := by
      simp [H'_map, Polynomial.toContinuousMapOn]
    rw [hval, Real.norm_eq_abs] at hle
    exact le_of_lt (lt_of_le_of_lt hle hQ)
  set N := Q.natDegree + 1
  let c : Fin N → ℝ := fun i => Q.coeff (i : ℕ) / ((i : ℕ) + 1 : ℝ)
  let P_poly : ℝ → ℝ := fun t => ∑ i : Fin N, c i * t ^ ((i : ℕ) + 1)
  have hP0 : P_poly 0 = 0 := by
    dsimp [P_poly]
    apply Finset.sum_eq_zero; intro i _; simp
  have hP_deriv : ∀ t : ℝ, HasDerivAt P_poly (Q.eval t) t := by
    intro t
    have hsum_eq : Q.eval t = ∑ i : Fin N, Q.coeff (i : ℕ) * t ^ (i : ℕ) := by
      rw [Polynomial.eval_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    rw [hsum_eq]
    dsimp only [P_poly]
    apply hasDerivAt_fin_sum
    intro i
    have hd1 : HasDerivAt (fun s : ℝ => c i * s ^ ((i : ℕ) + 1))
        (c i * ((((i : ℕ) + 1 : ℕ) : ℝ) * t ^ (i : ℕ))) t :=
      (hasDerivAt_pow ((i : ℕ) + 1) t).const_mul (c i)
    have hsimp : c i * ((((i : ℕ) + 1 : ℕ) : ℝ) * t ^ (i : ℕ)) = Q.coeff (i : ℕ) * t ^ (i : ℕ) := by
      dsimp [c]; push_cast
      have hne : ((i : ℕ) + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hne]
    rwa [hsimp] at hd1
  have hHP_diff : ∀ t : ℝ, HasDerivAt (fun s => H s - P_poly s) (H' t - Q.eval t) t :=
    fun t => (hH_deriv t).sub (hP_deriv t)
  have hHP_bound : ∀ t ∈ Icc (0 : ℝ) R, |H t - P_poly t| ≤ ε' * R := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | ht_pos
    · rw [← h0]; simp [hH0, hP0]; positivity
    · have hdiff_all : Differentiable ℝ (fun s => H s - P_poly s) := fun s => (hHP_diff s).differentiableAt
      obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope (fun s => H s - P_poly s) ht_pos
        hdiff_all.continuous.continuousOn hdiff_all.differentiableOn
      rw [(hHP_diff ξ).deriv, hH0, hP0, sub_self, sub_zero, sub_zero] at hslope
      have hξ_bound : |H' ξ - Q.eval ξ| ≤ ε' := by
        rw [abs_sub_comm]; exact hQ_pt ξ ⟨le_of_lt hξ.1, le_trans (le_of_lt hξ.2) ht.2⟩
      have heq : H t - P_poly t = (H' ξ - Q.eval ξ) * t := by
        rw [hslope]; exact (div_mul_cancel₀ _ (ne_of_gt ht_pos)).symm
      rw [heq, abs_mul, abs_of_pos ht_pos]
      calc |H' ξ - Q.eval ξ| * t ≤ ε' * t := mul_le_mul_of_nonneg_right hξ_bound (le_of_lt ht_pos)
        _ ≤ ε' * R := mul_le_mul_of_nonneg_left ht.2 (le_of_lt hε'_pos)
  refine ⟨N, c, ?_⟩
  intro g Δ
  have hg_eq_P : ∀ y : ℝ, g y = P_poly (Real.exp y) := by
    intro y; dsimp only [g, P_poly]
    apply Finset.sum_congr rfl; intro i _
    congr 1
    rw [← Real.exp_nat_mul, Nat.cast_add, Nat.cast_one]
  have hΔ_eq : ∀ y : ℝ, Δ y = H (Real.exp y) - P_poly (Real.exp y) := by
    intro y; dsimp only [Δ, H]
    rw [if_neg (not_le.mpr (Real.exp_pos y)), Real.log_exp, hg_eq_P]
  have hΔ_deriv : ∀ y : ℝ, HasDerivAt Δ ((H' (Real.exp y) - Q.eval (Real.exp y)) * Real.exp y) y := by
    intro y
    have hd := (hHP_diff (Real.exp y)).comp y (Real.hasDerivAt_exp y)
    exact hd.congr_of_eventuallyEq (Eventually.of_forall hΔ_eq)
  have hΔ_deriv_le : ∀ y ≤ M, |deriv Δ y| ≤ ε' * R := by
    intro y hy
    rw [(hΔ_deriv y).deriv, abs_mul, abs_of_pos (Real.exp_pos y)]
    have hexp_le : Real.exp y ≤ R := Real.exp_le_exp.mpr hy
    have h1 : |H' (Real.exp y) - Q.eval (Real.exp y)| ≤ ε' := by
      rw [abs_sub_comm]; exact hQ_pt (Real.exp y) ⟨le_of_lt (Real.exp_pos y), hexp_le⟩
    calc |H' (Real.exp y) - Q.eval (Real.exp y)| * Real.exp y
        ≤ ε' * Real.exp y := mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos y))
      _ ≤ ε' * R := mul_le_mul_of_nonneg_left hexp_le (le_of_lt hε'_pos)
  have hΔ_lip_tight : ∀ u v, u ≤ v → v ≤ M → |Δ v - Δ u| ≤ (ε' * R) * (v - u) := by
    intro u v huv hvM
    rcases eq_or_lt_of_le huv with rfl | hlt
    · simp
    · have hΔ_diff_all : Differentiable ℝ Δ := fun y => (hΔ_deriv y).differentiableAt
      obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope Δ hlt
        hΔ_diff_all.continuous.continuousOn hΔ_diff_all.differentiableOn
      have heq : Δ v - Δ u = deriv Δ ξ * (v - u) := by
        rw [hslope]; exact (div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hlt))).symm
      rw [heq, abs_mul, abs_of_pos (sub_pos.mpr hlt)]
      exact mul_le_mul_of_nonneg_right (hΔ_deriv_le ξ (le_trans (le_of_lt hξ.2) hvM)) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rw [hΔ_eq]
    exact le_trans (hHP_bound (Real.exp y) ⟨le_of_lt (Real.exp_pos y), Real.exp_le_exp.mpr hy⟩) hε'R_le
  · intro u v huv hvM
    exact le_trans (hΔ_lip_tight u v huv hvM)
      (mul_le_mul_of_nonneg_right hε'R_le (sub_nonneg.mpr huv))
  · intro z hz
    have hzM : z ≤ M := le_trans hz.2 hZM
    have ⟨hg_int, hg_gen⟩ := exp_sum_gen_eq X hBV c z
    have hg_diff_at : DifferentiableAt ℝ g z := by
      have hgP : g = fun y => P_poly (Real.exp y) := funext hg_eq_P
      rw [hgP]
      exact ((hP_deriv (Real.exp z)).comp z (Real.hasDerivAt_exp z)).differentiableAt
    have hderiv_sub : deriv F z - deriv g z = deriv Δ z := by
      have hd : HasDerivAt Δ (deriv F z - deriv g z) z := (hF_diff z).hasDerivAt.sub hg_diff_at.hasDerivAt
      exact hd.deriv.symm
    have hint_Δ : IntegrableOn (fun u => Δ (z + u) - Δ z) (Iio (0 : ℝ)) X.ν := by
      have heq : (fun u => Δ (z + u) - Δ z) = fun u => (F (z + u) - F z) - (g (z + u) - g z) := by
        ext u; dsimp [Δ]; ring
      rw [heq]; exact (hF_int z hz).sub hg_int
    have hint_sub : (∫ u in Iio (0 : ℝ), (F (z + u) - F z) ∂X.ν) -
        (∫ u in Iio (0 : ℝ), (g (z + u) - g z) ∂X.ν) =
        ∫ u in Iio (0 : ℝ), (Δ (z + u) - Δ z) ∂X.ν := by
      rw [← integral_sub (hF_int z hz) hg_int]
      apply setIntegral_congr_fun measurableSet_Iio; intro u _; dsimp [Δ]; ring
    have hsplit : Iio (0 : ℝ) = Iic (-1 : ℝ) ∪ Ioo (-1 : ℝ) 0 := by
      ext u; simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]; constructor
      · intro hu; by_cases h : u ≤ -1
        · exact Or.inl h
        · exact Or.inr ⟨by linarith, hu⟩
      · rintro (h | ⟨_, h⟩) <;> linarith
    have hdisj : Disjoint (Iic (-1 : ℝ)) (Ioo (-1 : ℝ) 0) := by
      rw [Set.disjoint_left]; intro u h1 h2; linarith [mem_Iic.mp h1, h2.1]
    have hint_neg_Δ : IntegrableOn (fun u => -(Δ (z + u) - Δ z)) (Iio (0 : ℝ)) X.ν := hint_Δ.neg
    have hjump_bound : ∫ u in Iio (0 : ℝ), -(Δ (z + u) - Δ z) ∂X.ν ≤
        (ε' * R) * (2 * (X.ν (Iic (-1 : ℝ))).toReal + ∫ u in Ioo (-1 : ℝ) 0, |u| ∂X.ν) := by
      rw [hsplit, setIntegral_union hdisj measurableSet_Ioo
        (hint_neg_Δ.mono_set (fun u hu => lt_of_le_of_lt (mem_Iic.mp hu) (by norm_num : (-1 : ℝ) < 0)))
        (hint_neg_Δ.mono_set (fun u hu => hu.2)), mul_add]
      apply add_le_add
      · calc ∫ u in Iic (-1 : ℝ), -(Δ (z + u) - Δ z) ∂X.ν
            ≤ ∫ _ in Iic (-1 : ℝ), (2 * (ε' * R)) ∂X.ν := by
              apply setIntegral_mono_on
                (hint_neg_Δ.mono_set (fun u hu => lt_of_le_of_lt (mem_Iic.mp hu) (by norm_num : (-1 : ℝ) < 0)))
                (integrableOn_const_of_lt_top hnu_1 _) measurableSet_Iic
              intro u hu
              have h1 : |Δ (z + u)| ≤ ε' * R := by
                rw [hΔ_eq]; exact hHP_bound _ ⟨le_of_lt (Real.exp_pos _), Real.exp_le_exp.mpr (by linarith [mem_Iic.mp hu])⟩
              have h2 : |Δ z| ≤ ε' * R := by
                rw [hΔ_eq]; exact hHP_bound _ ⟨le_of_lt (Real.exp_pos _), Real.exp_le_exp.mpr hzM⟩
              linarith [neg_abs_le (Δ (z + u)), le_abs_self (Δ z)]
          _ = (X.ν (Iic (-1 : ℝ))).toReal * (2 * (ε' * R)) := by
              rw [setIntegral_const, smul_eq_mul, Measure.real_def]
          _ = (ε' * R) * (2 * (X.ν (Iic (-1 : ℝ))).toReal) := by ring
      · calc ∫ u in Ioo (-1 : ℝ) 0, -(Δ (z + u) - Δ z) ∂X.ν
            ≤ ∫ u in Ioo (-1 : ℝ) 0, ((ε' * R) * |u|) ∂X.ν := by
              apply setIntegral_mono_on
                (hint_neg_Δ.mono_set (fun u hu => hu.2))
                ((nu_Ioo_abs_integrable X hBV).const_mul (ε' * R)) measurableSet_Ioo
              intro u hu
              have h1 := hΔ_lip_tight (z + u) z (by linarith [hu.2]) hzM
              have h2 : z - (z + u) = |u| := by rw [abs_of_neg hu.2]; ring
              rw [h2] at h1
              have h3 : -(Δ (z + u) - Δ z) = Δ z - Δ (z + u) := by ring
              rw [h3]
              exact (le_abs_self _).trans h1
          _ = (ε' * R) * ∫ u in Ioo (-1 : ℝ) 0, |u| ∂X.ν := integral_const_mul _ _
    have hdrift_bound : -(X.drift * deriv Δ z) ≤ (ε' * R) * |X.drift| := by
      calc -(X.drift * deriv Δ z) ≤ |-(X.drift * deriv Δ z)| := le_abs_self _
        _ = |X.drift| * |deriv Δ z| := by rw [abs_neg, abs_mul]
        _ ≤ |X.drift| * (ε' * R) := mul_le_mul_of_nonneg_left (hΔ_deriv_le z hzM) (abs_nonneg _)
        _ = (ε' * R) * |X.drift| := mul_comm _ _
    rw [← hg_gen]
    have hrew : (X.drift * deriv g z + ∫ u in Iio (0 : ℝ), (g (z + u) - g z) ∂X.ν) -
        (X.drift * deriv F z + ∫ u in Iio (0 : ℝ), (F (z + u) - F z) ∂X.ν) =
        -(X.drift * deriv Δ z) + ∫ u in Iio (0 : ℝ), -(Δ (z + u) - Δ z) ∂X.ν := by
      rw [integral_neg, ← hint_sub, ← hderiv_sub]; ring
    rw [hrew]
    have htot : (ε' * R) * |X.drift| + (ε' * R) * (2 * (X.ν (Iic (-1 : ℝ))).toReal + ∫ u in Ioo (-1 : ℝ) 0, |u| ∂X.ν) ≤
        (ε' * R) * K_gen := by
      dsimp [K_gen]
      have : 0 ≤ ε' * R := by positivity
      linarith
    linarith

/-! ### Section 5: Dividend measure, ruin time measurability, and exponential step expectation -/

private def DPlus (D : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  rightLimit D t ω

private def UPlus (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x + X.X t ω - DPlus D t ω

private def E_surv (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : Set Ω :=
  {ω | (t : ℝ≥0∞) < ruinTime X x D ω}

private lemma D_nonneg {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D) (t : ℝ≥0) (ω : Ω) :
    0 ≤ D t ω := by
  rw [← hD.1 ω]
  exact hD.2.1 ω zero_le

private lemma D_le_DPlus {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D) (t : ℝ≥0) (ω : Ω) :
    D t ω ≤ DPlus D t ω := by
  have : Nonempty (Ioi t) := ⟨⟨t + 1, lt_add_of_pos_right t zero_lt_one⟩⟩
  exact le_ciInf fun s => hD.2.1 ω (le_of_lt s.2)

private lemma DPlus_bddBelow {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D) (t : ℝ≥0) (ω : Ω) :
    BddBelow (Set.range fun s : Ioi t => D s ω) :=
  ⟨0, by rintro _ ⟨s, rfl⟩; exact D_nonneg hD s.1 ω⟩

private lemma stieltjes_D_eq {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    ∃ hf : Monotone (fun t : ℝ => D t.toNNReal ω),
      dividendMeasure D ω = hf.stieltjesFunction.measure ∧
      (∀ t < 0, hf.stieltjesFunction t = 0) ∧
      (∀ t : ℝ≥0, hf.stieltjesFunction (t : ℝ) = DPlus D t ω) := by
  have hf : Monotone (fun t : ℝ => D t.toNNReal ω) :=
    fun a b hab => hD.2.1 ω (Real.toNNReal_mono hab)
  refine ⟨hf, dif_pos hf, ?_, ?_⟩
  · intro t ht
    rw [Monotone.stieltjesFunction_eq]
    apply rightLim_eq_of_tendsto
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT ht] with s hs
    exact ((congrArg (fun u => D u ω) (Real.toNNReal_of_nonpos (le_of_lt hs.2))).trans (hD.1 ω)).symm
  · intro t
    rw [Monotone.stieltjesFunction_eq]
    apply rightLim_eq_of_tendsto
    rw [tendsto_order]
    constructor
    · intro b hb
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hyt : t < y.toNNReal := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal y (le_trans t.coe_nonneg (le_of_lt (mem_Ioi.mp hy)))]
        exact mem_Ioi.mp hy
      exact lt_of_lt_of_le hb (ciInf_le (DPlus_bddBelow hD t ω) ⟨y.toNNReal, hyt⟩)
    · intro b hb
      have : Nonempty (Ioi t) := ⟨⟨t + 1, lt_add_of_pos_right t zero_lt_one⟩⟩
      obtain ⟨s, hs⟩ := exists_lt_of_ciInf_lt hb
      have hts : (t : ℝ) < (s.1 : ℝ) := s.2
      filter_upwards [Ioo_mem_nhdsGT hts] with y hy
      have hys : y.toNNReal ≤ s.1 := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal y (le_trans t.coe_nonneg (le_of_lt hy.1))]
        exact le_of_lt hy.2
      exact lt_of_le_of_lt (hD.2.1 ω hys) hs

private lemma dividendMeasure_singleton_zero {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    (dividendMeasure D ω) {0} = ENNReal.ofReal (DPlus D 0 ω) := by
  obtain ⟨hf, hmeas, hneg, hnn⟩ := stieltjes_D_eq hD ω
  rw [hmeas, StieltjesFunction.measure_singleton]
  have hleft : Function.leftLim hf.stieltjesFunction 0 = 0 := by
    apply leftLim_eq_of_tendsto
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hneg t (mem_Iio.mp ht)).symm
  have h0 : hf.stieltjesFunction ((0 : ℝ≥0) : ℝ) = DPlus D 0 ω := hnn 0
  simp only [NNReal.coe_zero] at h0
  rw [h0, hleft, sub_zero]

private lemma dividendMeasure_Ioc {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D) (ω : Ω)
    (a b : ℝ≥0) :
    (dividendMeasure D ω) (Ioc (a : ℝ) (b : ℝ)) = ENNReal.ofReal (DPlus D b ω - DPlus D a ω) := by
  obtain ⟨hf, hmeas, _, hnn⟩ := stieltjes_D_eq hD ω
  rw [hmeas, StieltjesFunction.measure_Ioc, hnn b, hnn a]

private lemma dividendMeasure_Ioo_le {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D) (ω : Ω)
    (a b : ℝ≥0) (hb : 0 < b) :
    (dividendMeasure D ω) (Ioo (a : ℝ) (b : ℝ)) ≤ ENNReal.ofReal (D b ω - DPlus D a ω) := by
  obtain ⟨hf, hmeas, _, hnn⟩ := stieltjes_D_eq hD ω
  rw [hmeas, StieltjesFunction.measure_Ioo, hnn a]
  apply ENNReal.ofReal_le_ofReal
  have hbR : (0 : ℝ) < (b : ℝ) := hb
  have hleft : Function.leftLim hf.stieltjesFunction (b : ℝ) = D b ω := by
    apply leftLim_eq_of_tendsto
    rw [tendsto_order]
    constructor
    · intro c hc
      have hcont := hD.2.2.1 ω b
      rw [ContinuousWithinAt, tendsto_order] at hcont
      have hev := (hcont.1 c hc)
      rw [eventually_nhdsWithin_iff] at hev
      have hmap : Tendsto Real.toNNReal (𝓝 (b : ℝ)) (𝓝 b) := by
        simpa [Real.toNNReal_coe] using continuous_real_toNNReal.continuousAt.tendsto (x := (b : ℝ))
      filter_upwards [nhdsWithin_le_nhds (hmap.eventually hev), Ioo_mem_nhdsLT hbR] with y hy1 hy2
      have hyb : y.toNNReal ≤ b := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal y (le_of_lt hy2.1)]
        exact le_of_lt hy2.2
      have hnn_y : hf.stieltjesFunction (y.toNNReal : ℝ) = DPlus D y.toNNReal ω := hnn y.toNNReal
      rw [Real.coe_toNNReal y (le_of_lt hy2.1)] at hnn_y
      rw [hnn_y]
      exact lt_of_lt_of_le (hy1 hyb) (D_le_DPlus hD y.toNNReal ω)
    · intro c hc
      filter_upwards [Ioo_mem_nhdsLT hbR] with y hy
      have hnn_y : hf.stieltjesFunction (y.toNNReal : ℝ) = DPlus D y.toNNReal ω := hnn y.toNNReal
      rw [Real.coe_toNNReal y (le_of_lt hy.1)] at hnn_y
      rw [hnn_y]
      set m : ℝ≥0 := ⟨(y + (b : ℝ)) / 2, by linarith [hy.1, hbR]⟩
      have hym : y.toNNReal < m := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal y (le_of_lt hy.1)]
        change y < (y + (b : ℝ)) / 2; linarith [hy.2]
      have hmb : m ≤ b := by
        change (y + (b : ℝ)) / 2 ≤ (b : ℝ); linarith [hy.2]
      exact lt_of_le_of_lt (le_trans (ciInf_le (DPlus_bddBelow hD _ ω) ⟨m, hym⟩) (hD.2.1 ω hmb)) hc
  rw [hleft]

private lemma UPlus_nonneg_of_admissible {X : SpectrallyNegativeLevy P 𝓕} {x : ℝ} {D : ℝ≥0 → Ω → ℝ}
    (hD : IsAdmissible X x D) (ω : Ω) (t : ℝ≥0) (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ UPlus X x D t ω := by
  have h := hD.2 ω t ht
  unfold UPlus DPlus riskProcess at *
  linarith

private lemma riskProcess_nonneg_of_lt_ruin {X : SpectrallyNegativeLevy P 𝓕} {x : ℝ} {D : ℝ≥0 → Ω → ℝ}
    {ω : Ω} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ riskProcess X x D t ω := by
  by_contra hneg
  push Not at hneg
  exact not_le_of_gt ht (iInf₂_le t hneg)

private lemma ruinTime_eq_rat_iInf (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    ruinTime X x D ω =
      ⨅ (q : ℚ), if 0 ≤ q ∧ riskProcess X x D (q : ℝ).toNNReal ω < 0 then
        ((q : ℝ).toNNReal : ℝ≥0∞) else ⊤ := by
  apply le_antisymm
  · refine le_iInf fun q => ?_
    split_ifs with hq
    · exact iInf₂_le (q : ℝ).toNNReal hq.2
    · exact le_top
  · refine le_iInf₂ fun t ht => ?_
    set η := -(riskProcess X x D t ω) / 2
    have hη : 0 < η := by dsimp [η]; linarith
    have hrc := X.rightCont ω t
    rw [Metric.continuousWithinAt_iff] at hrc
    obtain ⟨δ, hδ_pos, hδ⟩ := hrc η hη
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεR : (0 : ℝ) < (ε : ℝ) := hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
      (lt_min (lt_add_of_pos_right (t : ℝ) hδ_pos) (lt_add_of_pos_right (t : ℝ) hεR))
    have hq_nn : 0 ≤ q := by exact_mod_cast le_trans t.coe_nonneg (le_of_lt hq1)
    have hqR_nn : 0 ≤ (q : ℝ) := by exact_mod_cast hq_nn
    set sq := (q : ℝ).toNNReal
    have htsq : t ≤ sq := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hqR_nn]; exact le_of_lt hq1
    have hdist : dist sq t < δ := by
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr htsq)),
          Real.coe_toNNReal _ hqR_nn]
      linarith [lt_of_lt_of_le hq2 (min_le_left _ _)]
    have hX_near := hδ htsq hdist
    rw [Real.dist_eq] at hX_near
    have hD_mono : D t ω ≤ D sq ω := hD.2.1 ω htsq
    have hU_neg : riskProcess X x D sq ω < 0 := by
      have := (abs_lt.mp hX_near).2
      dsimp [η] at this
      unfold riskProcess at ht this ⊢
      linarith
    calc (⨅ q : ℚ, if 0 ≤ q ∧ riskProcess X x D (q : ℝ).toNNReal ω < 0 then ((q : ℝ).toNNReal : ℝ≥0∞) else ⊤)
        ≤ if 0 ≤ q ∧ riskProcess X x D sq ω < 0 then (sq : ℝ≥0∞) else ⊤ := iInf_le _ q
      _ = (sq : ℝ≥0∞) := if_pos ⟨hq_nn, hU_neg⟩
      _ ≤ ((t + ε : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, Real.coe_toNNReal _ hqR_nn]
          change (q : ℝ) ≤ (t : ℝ) + (ε : ℝ)
          exact le_of_lt (lt_of_lt_of_le hq2 (min_le_right _ _))
      _ = (t : ℝ≥0∞) + (ε : ℝ≥0∞) := ENNReal.coe_add t ε

private lemma measurable_ruinTime (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D) :
    Measurable (ruinTime X x D) := by
  have heq : ruinTime X x D = fun ω =>
      ⨅ (q : ℚ), if 0 ≤ q ∧ riskProcess X x D (q : ℝ).toNNReal ω < 0 then
        ((q : ℝ).toNNReal : ℝ≥0∞) else ⊤ := funext (ruinTime_eq_rat_iInf X x hD)
  rw [heq]
  apply Measurable.iInf
  intro q
  by_cases hq0 : 0 ≤ q
  · have hD_meas : Measurable (D (q : ℝ).toNNReal) := (hD.2.2.2 _).mono (𝓕.le _) le_rfl
    have hU_meas : Measurable (riskProcess X x D (q : ℝ).toNNReal) :=
      ((measurable_const.add (X_measurable X _)).sub hD_meas)
    have hsimp : (fun ω => if 0 ≤ q ∧ riskProcess X x D (q : ℝ).toNNReal ω < 0 then
          ((q : ℝ).toNNReal : ℝ≥0∞) else ⊤) =
        fun ω => if riskProcess X x D (q : ℝ).toNNReal ω < 0 then ((q : ℝ).toNNReal : ℝ≥0∞) else ⊤ := by
      ext ω; simp [hq0]
    rw [hsimp]
    exact Measurable.ite (measurableSet_lt hU_meas measurable_const) measurable_const measurable_const
  · have hsimp : (fun ω => if 0 ≤ q ∧ riskProcess X x D (q : ℝ).toNNReal ω < 0 then
          ((q : ℝ).toNNReal : ℝ≥0∞) else ⊤) = fun _ => ⊤ := by
      ext ω; simp [hq0]
    rw [hsimp]; exact measurable_const

private lemma measurableSet_le_ruinTime (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) ≤ ruinTime X x D ω} := by
  have heq : {ω | (t : ℝ≥0∞) ≤ ruinTime X x D ω} =
      ⋂ (q : ℚ), {ω | (0 ≤ q ∧ (q : ℝ).toNNReal < t) → 0 ≤ riskProcess X x D (q : ℝ).toNNReal ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_iInter, ruinTime_eq_rat_iInf X x hD ω, le_iInf_iff]
    constructor
    · intro h q ⟨hq0, hqt⟩
      by_contra hneg; push Not at hneg
      have h1 := h q
      rw [if_pos ⟨hq0, hneg⟩, ENNReal.coe_le_coe] at h1
      exact not_le_of_gt hqt h1
    · intro h q
      split_ifs with hq
      · rw [ENNReal.coe_le_coe]
        by_contra hlt; push Not at hlt
        exact not_lt_of_ge (h q ⟨hq.1, hlt⟩) hq.2
      · exact le_top
  rw [heq]
  apply MeasurableSet.iInter
  intro q
  by_cases hq : 0 ≤ q ∧ (q : ℝ).toNNReal < t
  · have hsub : {ω | (0 ≤ q ∧ (q : ℝ).toNNReal < t) → 0 ≤ riskProcess X x D (q : ℝ).toNNReal ω} =
        {ω | 0 ≤ riskProcess X x D (q : ℝ).toNNReal ω} := by ext ω; simp [hq]
    rw [hsub]
    have hX_m : Measurable[𝓕 t] (X.X (q : ℝ).toNNReal) :=
      (X.adapted _).mono (𝓕.mono (le_of_lt hq.2)) le_rfl
    have hD_m : Measurable[𝓕 t] (D (q : ℝ).toNNReal) :=
      (hD.2.2.2 _).mono (𝓕.mono (le_of_lt hq.2)) le_rfl
    exact measurableSet_le measurable_const ((measurable_const.add hX_m).sub hD_m)
  · have hsub : {ω | (0 ≤ q ∧ (q : ℝ).toNNReal < t) → 0 ≤ riskProcess X x D (q : ℝ).toNNReal ω} = univ := by
      ext ω; simp [hq]
    rw [hsub]; exact MeasurableSet.univ

private lemma measurable_D_at_stop {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D)
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) :
    Measurable (fun ω => D (τ ω) ω) := by
  let approx : ℕ → Ω → ℝ≥0 := fun j ω =>
    (Nat.floor ((τ ω : ℝ) * (2 : ℝ) ^ j) : ℝ≥0) / ((2 : ℝ≥0) ^ j)
  have hmeas_j : ∀ j : ℕ, Measurable (fun ω => D (approx j ω) ω) := by
    intro j
    have hscaled_m : Measurable (fun ω => (τ ω : ℝ) * (2 : ℝ) ^ j) :=
      (continuous_id.mul continuous_const).measurable.comp (measurable_subtype_coe.comp hτ)
    intro s hs
    have hpre : (fun ω => D (approx j ω) ω) ⁻¹' s =
        ⋃ k : ℕ, ({ω | (k : ℝ) ≤ (τ ω : ℝ) * (2 : ℝ) ^ j ∧ (τ ω : ℝ) * (2 : ℝ) ^ j < (k : ℝ) + 1} ∩
          {ω | D ((k : ℝ≥0) / (2 : ℝ≥0) ^ j) ω ∈ s}) := by
      ext ω; simp only [mem_preimage, mem_iUnion, mem_inter_iff, Set.mem_ofPred_eq]
      have hnn : 0 ≤ (τ ω : ℝ) * (2 : ℝ) ^ j := by positivity
      constructor
      · intro h
        refine ⟨Nat.floor ((τ ω : ℝ) * (2 : ℝ) ^ j), ⟨Nat.floor_le hnn, Nat.lt_floor_add_one _⟩, h⟩
      · rintro ⟨k, ⟨hk1, hk2⟩, h⟩
        have hk_eq : Nat.floor ((τ ω : ℝ) * (2 : ℝ) ^ j) = k :=
          (Nat.floor_eq_iff hnn).mpr ⟨hk1, hk2⟩
        dsimp only [approx]
        rwa [hk_eq]
    rw [hpre]
    refine MeasurableSet.iUnion fun k => MeasurableSet.inter ?_ ?_
    · exact (measurableSet_le measurable_const hscaled_m).inter
        (measurableSet_lt hscaled_m measurable_const)
    · exact ((hD.2.2.2 _).mono (𝓕.le _) le_rfl) hs
  refine measurable_of_tendsto_metrizable hmeas_j (tendsto_pi_nhds.mpr fun ω => ?_)
  have hle : ∀ j : ℕ, approx j ω ≤ τ ω := by
    intro j
    rw [← NNReal.coe_le_coe]; dsimp [approx]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    exact Nat.floor_le (by positivity)
  have htend_approx : Tendsto (fun j => approx j ω) atTop (𝓝 (τ ω)) := by
    rw [← NNReal.tendsto_coe]
    have hhi : Tendsto (fun j : ℕ => (τ ω : ℝ) - (1 / 2 : ℝ) ^ j) atTop (𝓝 (τ ω : ℝ)) := by
      simpa [sub_zero] using (tendsto_const_nhds (x := (τ ω : ℝ))).sub
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hhi tendsto_const_nhds ?_ ?_
    · intro j; dsimp only [approx]; push_cast
      have hlt := Nat.lt_floor_add_one ((τ ω : ℝ) * (2 : ℝ) ^ j)
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
      have hpow : (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j = 1 := by
        rw [← mul_pow]; norm_num
      rw [le_div_iff₀ h2pos]
      linarith
    · intro j; exact NNReal.coe_le_coe.mpr (hle j)
  have hcont := hD.2.2.1 ω (τ ω)
  exact hcont.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htend_approx
    (Eventually.of_forall hle))

private lemma E_surv_measurable_gt (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D) {s r : ℝ≥0} (hsr : s < r) :
    MeasurableSet[𝓕 r] (E_surv X x D s) := by
  have heq : E_surv X x D s =
      ⋃ n : ℕ, {ω | ((min r (s + ⟨1 / (n + 1 : ℝ), by positivity⟩) : ℝ≥0) : ℝ≥0∞) ≤ ruinTime X x D ω} := by
    ext ω; simp only [E_surv, Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hlt
      by_cases htop : ruinTime X x D ω = ⊤
      · exact ⟨0, by rw [htop]; exact le_top⟩
      · have hs_lt_toNN : (s : ℝ) < ((ruinTime X x D ω).toNNReal : ℝ) := by
          have : (s : ℝ≥0∞) < ((ruinTime X x D ω).toNNReal : ℝ≥0∞) := by
            rwa [ENNReal.coe_toNNReal htop]
          exact ENNReal.coe_lt_coe.mp this
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hs_lt_toNN)
        refine ⟨n, ?_⟩
        rw [← ENNReal.coe_toNNReal htop, ENNReal.coe_le_coe]
        refine le_trans (min_le_right _ _) ?_
        change (s : ℝ) + 1 / (n + 1 : ℝ) ≤ ((ruinTime X x D ω).toNNReal : ℝ)
        linarith
    · rintro ⟨n, hn⟩
      have hlt_min : s < min r (s + ⟨1 / (n + 1 : ℝ), by positivity⟩) :=
        lt_min hsr (by
          change (s : ℝ) < (s : ℝ) + 1 / (n + 1 : ℝ)
          linarith [show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity])
      exact lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hlt_min) hn
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  exact 𝓕.mono (min_le_left _ _) _ (measurableSet_le_ruinTime X x hD _)

private lemma DPlus_measurable_gt {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D)
    {s r : ℝ≥0} (hsr : s < r) :
    Measurable[𝓕 r] (DPlus D s) := by
  let S_rat := {q : ℚ // (s : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (r : ℝ)}
  obtain ⟨q₀, hq₀1, hq₀2⟩ := exists_rat_btwn (show (s : ℝ) < (r : ℝ) from hsr)
  have : Nonempty S_rat := ⟨⟨q₀, hq₀1, le_of_lt hq₀2⟩⟩
  have heq : DPlus D s = fun ω =>
      (⨅ q : S_rat, ENNReal.ofReal (D (q.1 : ℝ).toNNReal ω)).toReal := by
    ext ω
    have h1 : DPlus D s ω = ⨅ q : S_rat, D (q.1 : ℝ).toNNReal ω := by
      apply le_antisymm
      · refine le_ciInf fun q => ?_
        have hsq : s < (q.1 : ℝ).toNNReal := by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (le_trans s.coe_nonneg (le_of_lt q.2.1))]
          exact q.2.1
        exact ciInf_le (DPlus_bddBelow hD s ω) ⟨(q.1 : ℝ).toNNReal, hsq⟩
      · refine le_ciInf fun u => ?_
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min (show (s : ℝ) < (u.1 : ℝ) from u.2) (show (s : ℝ) < (r : ℝ) from hsr))
        have hq_mem : (s : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (r : ℝ) := ⟨hq1, le_of_lt (lt_of_lt_of_le hq2 (min_le_right _ _))⟩
        have hqu : (q : ℝ).toNNReal ≤ u.1 := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (le_trans s.coe_nonneg (le_of_lt hq1))]
          exact le_of_lt (lt_of_lt_of_le hq2 (min_le_left _ _))
        have hbdd : BddBelow (Set.range fun q' : S_rat => D (q'.1 : ℝ).toNNReal ω) :=
          ⟨0, by rintro _ ⟨q', rfl⟩; exact D_nonneg hD _ ω⟩
        exact le_trans (ciInf_le hbdd ⟨q, hq_mem⟩) (hD.2.1 ω hqu)
    have h2 : ENNReal.ofReal (⨅ q : S_rat, D (q.1 : ℝ).toNNReal ω) =
        ⨅ q : S_rat, ENNReal.ofReal (D (q.1 : ℝ).toNNReal ω) := by
      apply le_antisymm
      · refine le_iInf fun q => ENNReal.ofReal_le_ofReal ?_
        exact ciInf_le ⟨0, by rintro _ ⟨q', rfl⟩; exact D_nonneg hD _ ω⟩ q
      · set val := ⨅ q : S_rat, ENNReal.ofReal (D (q.1 : ℝ).toNNReal ω)
        have hlt_top : val < ⊤ := lt_of_le_of_lt (iInf_le _ ⟨q₀, hq₀1, le_of_lt hq₀2⟩) ENNReal.ofReal_lt_top
        rw [← ENNReal.ofReal_toReal (ne_of_lt hlt_top)]
        apply ENNReal.ofReal_le_ofReal
        refine le_ciInf fun q => ?_
        have hle : val ≤ ENNReal.ofReal (D (q.1 : ℝ).toNNReal ω) := iInf_le _ q
        exact (ENNReal.toReal_le_of_le_ofReal (D_nonneg hD _ ω) hle)
    have hnn_inf : 0 ≤ ⨅ q : S_rat, D (q.1 : ℝ).toNNReal ω :=
      le_ciInf fun q => D_nonneg hD _ ω
    rw [h1, ← h2, ENNReal.toReal_ofReal hnn_inf]
  rw [heq]
  refine ENNReal.measurable_toReal.comp (Measurable.iInf fun q => ENNReal.measurable_ofReal.comp ?_)
  have hqr : (q.1 : ℝ).toNNReal ≤ r := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (le_trans s.coe_nonneg (le_of_lt q.2.1))]
    exact q.2.2
  exact (hD.2.2.2 _).mono (𝓕.mono hqr) le_rfl

private lemma exp_step_expectation (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x Z_max m : ℝ) (_hZ : 0 ≤ Z_max) (hm : 0 ≤ m)
    {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D) {s t : ℝ≥0} (hst : s < t) :
    let z_clip : Ω → ℝ := fun ω => min (max 0 (UPlus X x D s ω)) Z_max
    ∫ ω, (E_surv X x D s).indicator
        (fun ω => Real.exp (m * (z_clip ω + (X.X t ω - X.X s ω)))) ω ∂P =
      (∫ ω, (E_surv X x D s).indicator (fun ω => Real.exp (m * z_clip ω)) ω ∂P) *
        Real.exp (((t : ℝ) - (s : ℝ)) * X.ψ m) := by
  have : IsProbabilityMeasure P := X.isProbability
  intro z_clip
  let A : Ω → ℝ := fun ω => (E_surv X x D s).indicator (fun ω => Real.exp (m * z_clip ω)) ω
  have hA_meas_gt : ∀ {r : ℝ≥0}, s < r → Measurable[𝓕 r] A := by
    intro r hsr
    have hU_m : Measurable[𝓕 r] (UPlus X x D s) :=
      ((measurable_const.add ((X.adapted s).mono (𝓕.mono (le_of_lt hsr)) le_rfl)).sub
        (DPlus_measurable_gt hD hsr))
    have hz_m : Measurable[𝓕 r] z_clip := (measurable_const.max hU_m).min measurable_const
    exact (Real.measurable_exp.comp (measurable_const.mul hz_m)).indicator (E_surv_measurable_gt X x hD hsr)
  have hA_meas : Measurable A := (hA_meas_gt hst).mono (𝓕.le t) le_rfl
  have hA_bdd : ∀ ω, 0 ≤ A ω ∧ A ω ≤ Real.exp (m * Z_max) := by
    intro ω; dsimp only [A]
    by_cases hω : ω ∈ E_surv X x D s
    · rw [Set.indicator_of_mem hω]
      refine ⟨le_of_lt (Real.exp_pos _), Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (min_le_right _ _) hm)⟩
    · rw [Set.indicator_of_notMem hω]; exact ⟨le_rfl, le_of_lt (Real.exp_pos _)⟩
  obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt (sub_pos.mpr (show (s : ℝ) < (t : ℝ) from hst))
  let rn : ℕ → ℝ≥0 := fun n => s + ⟨1 / (n + N₀ + 1 : ℝ), by positivity⟩
  have hrn_gt : ∀ n, s < rn n := fun n => by
    change (s : ℝ) < (s : ℝ) + 1 / (n + N₀ + 1 : ℝ)
    linarith [show (0 : ℝ) < 1 / (n + N₀ + 1 : ℝ) by positivity]
  have hrn_lt : ∀ n, rn n < t := fun n => by
    change (s : ℝ) + 1 / (n + N₀ + 1 : ℝ) < (t : ℝ)
    have hle : 1 / (n + N₀ + 1 : ℝ) ≤ 1 / (N₀ + 1 : ℝ) :=
      one_div_le_one_div_of_le
        (show (0 : ℝ) < (N₀ : ℝ) + 1 by positivity)
        (show (N₀ : ℝ) + 1 ≤ (n : ℝ) + (N₀ : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  have hrn_tend : Tendsto rn atTop (𝓝 s) := by
    rw [← NNReal.tendsto_coe]
    have h1 : Tendsto (fun n : ℕ => 1 / ((n + N₀ : ℕ) + 1 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat N₀)
    have h2 : Tendsto (fun n : ℕ => (s : ℝ) + 1 / ((n + N₀ : ℕ) + 1 : ℝ)) atTop (𝓝 (s : ℝ)) := by
      simpa [add_zero] using (tendsto_const_nhds (x := (s : ℝ))).add h1
    refine h2.congr fun n => ?_
    change (s : ℝ) + 1 / ((n + N₀ : ℕ) + 1 : ℝ) = (s : ℝ) + 1 / (n + N₀ + 1 : ℝ)
    push_cast; ring
  have hstep : ∀ n : ℕ,
      ∫ ω, A ω * Real.exp (m * (X.X t ω - X.X (rn n) ω)) ∂P =
        (∫ ω, A ω ∂P) * Real.exp (((t : ℝ) - (rn n : ℝ)) * X.ψ m) := by
    intro n
    set Yn : Ω → ℝ := fun ω => Real.exp (m * (X.X t ω - X.X (rn n) ω))
    have hind := (X.indepIncrements (rn n) t (le_of_lt (hrn_lt n))).symm
    have hYn_comap : MeasurableSpace.comap Yn inferInstance ≤
        MeasurableSpace.comap (fun ω => X.X t ω - X.X (rn n) ω) inferInstance := by
      have : Yn = (fun u => Real.exp (m * u)) ∘ (fun ω => X.X t ω - X.X (rn n) ω) := rfl
      rw [this, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (Real.measurable_exp.comp (measurable_const.mul measurable_id)).comap_le
    have hind_fun : IndepFun A Yn P :=
      (IndepFun_iff_Indep A Yn P).mpr
        (indep_of_indep_of_le_right (indep_of_indep_of_le_left hind (hA_meas_gt (hrn_gt n)).comap_le) hYn_comap)
    have hmul := hind_fun.integral_mul_eq_mul_integral hA_meas.aestronglyMeasurable
      ((Real.measurable_exp.comp (measurable_const.mul ((X_measurable X t).sub (X_measurable X (rn n))))).aestronglyMeasurable)
    have hid_law : IdentDistrib Yn (fun ω => Real.exp (m * X.X (t - rn n) ω)) P P :=
      (X.stationaryIncrements (rn n) t (le_of_lt (hrn_lt n))).comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
    have hlap := (X.laplace (t - rn n) m hm).2
    rw [NNReal.coe_sub (le_of_lt (hrn_lt n))] at hlap
    change ∫ ω, (A * Yn) ω ∂P = _
    rw [hmul, hid_law.integral_eq, hlap]; rfl
  set K_dom := Real.exp (m * Z_max) * Real.exp (m * (max 0 X.drift * (t : ℝ)))
  have hLHS_tend : Tendsto (fun n => ∫ ω, A ω * Real.exp (m * (X.X t ω - X.X (rn n) ω)) ∂P)
      atTop (𝓝 (∫ ω, A ω * Real.exp (m * (X.X t ω - X.X s ω)) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => K_dom)
    · intro n
      exact (hA_meas.mul (Real.measurable_exp.comp (measurable_const.mul ((X_measurable X t).sub (X_measurable X (rn n)))))).aestronglyMeasurable
    · exact integrable_const K_dom
    · intro n
      filter_upwards [pathBV_ae X hBV] with ω hω
      have hinc : X.X t ω - X.X (rn n) ω ≤ max 0 X.drift * (t : ℝ) := by
        calc X.X t ω - X.X (rn n) ω ≤ X.drift * ((t : ℝ) - (rn n : ℝ)) := hω (rn n) t (le_of_lt (hrn_lt n))
          _ ≤ max 0 X.drift * ((t : ℝ) - (rn n : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_right 0 X.drift) (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (le_of_lt (hrn_lt n))))
          _ ≤ max 0 X.drift * (t : ℝ) :=
              mul_le_mul_of_nonneg_left (by linarith [(rn n).coe_nonneg]) (le_max_left 0 X.drift)
      have hnn : 0 ≤ A ω * Real.exp (m * (X.X t ω - X.X (rn n) ω)) :=
        mul_nonneg (hA_bdd ω).1 (le_of_lt (Real.exp_pos _))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul (hA_bdd ω).2 (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hinc hm))
        (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
    · filter_upwards with ω
      have hrn_nhds : Tendsto rn atTop (𝓝[≥] s) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hrn_tend
          (Eventually.of_forall fun n => le_of_lt (hrn_gt n))
      have hX_tend : Tendsto (fun n => X.X (rn n) ω) atTop (𝓝 (X.X s ω)) :=
        (X.rightCont ω s).tendsto.comp hrn_nhds
      exact tendsto_const_nhds.mul
        (Real.continuous_exp.continuousAt.tendsto.comp (tendsto_const_nhds.mul (tendsto_const_nhds.sub hX_tend)))
  have hRHS_tend : Tendsto (fun n => (∫ ω, A ω ∂P) * Real.exp (((t : ℝ) - (rn n : ℝ)) * X.ψ m))
      atTop (𝓝 ((∫ ω, A ω ∂P) * Real.exp (((t : ℝ) - (s : ℝ)) * X.ψ m))) :=
    tendsto_const_nhds.mul (Real.continuous_exp.continuousAt.tendsto.comp
      ((tendsto_const_nhds.sub (NNReal.tendsto_coe.mpr hrn_tend)).mul tendsto_const_nhds))
  have hlim := tendsto_nhds_unique hLHS_tend (by simp_rw [hstep]; exact hRHS_tend)
  rw [← hlim]
  apply integral_congr_ae
  filter_upwards with ω
  dsimp only [A]
  by_cases hω : ω ∈ E_surv X x D s
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, mul_add, Real.exp_add]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]

private lemma F_step_expectation_bound (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) {q : ℝ} (hq : 0 < q)
    {x Z_max T ε ε₁ B₀ : ℝ} (hZ : 0 ≤ Z_max) (hT : 0 < T) (hε : 0 < ε) (hε₁ : 0 < ε₁)
    {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D)
    {F : ℝ → ℝ} (hF_mono : Monotone F) (hF_nn : ∀ y, 0 ≤ F y) (hF_bdd : ∀ y, F y ≤ B₀)
    (hF_gen : ∀ z ∈ Icc (0 : ℝ) Z_max,
      X.drift * deriv F z + ∫ u in Iio (0 : ℝ), (F (z + u) - F z) ∂X.ν - q * F z ≤ ε)
    {N : ℕ} {c : Fin N → ℝ}
    (hΔ_bdd : ∀ y ≤ Z_max + X.drift * T + 1, |F y - ∑ i : Fin N, c i * Real.exp (((i : ℕ) + 1 : ℝ) * y)| ≤ ε₁)
    (hΔ_lip : ∀ u v, u ≤ v → v ≤ Z_max + X.drift * T + 1 →
      |(F v - ∑ i : Fin N, c i * Real.exp (((i : ℕ) + 1 : ℝ) * v)) -
       (F u - ∑ i : Fin N, c i * Real.exp (((i : ℕ) + 1 : ℝ) * u))| ≤ ε₁ * (v - u))
    (hgen_approx : ∀ z ∈ Icc (0 : ℝ) Z_max,
      (∑ i : Fin N, c i * Real.exp (((i : ℕ) + 1 : ℝ) * z) * X.ψ ((i : ℕ) + 1 : ℝ)) -
        (X.drift * deriv F z + ∫ u in Iio (0 : ℝ), (F (z + u) - F z) ∂X.ν) ≤ ε₁) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ (s t : ℝ≥0), s < t → (t : ℝ) - (s : ℝ) ≤ T → (t : ℝ) - (s : ℝ) < h₀ →
      let h := (t : ℝ) - (s : ℝ)
      let z_clip : Ω → ℝ := fun ω => min (max 0 (UPlus X x D s ω)) Z_max
      Real.exp (-(q * h)) *
          (∫ ω, (E_surv X x D s).indicator (fun ω => F (z_clip ω + (X.X t ω - X.X s ω))) ω ∂P) -
        (∫ ω, (E_surv X x D s).indicator (fun ω => F (z_clip ω)) ω ∂P) ≤
        h * (ε + 2 * ε₁) + ε₁ * (X.drift * h +
          ((∫ ω, (X.drift * (t : ℝ) - X.X t ω) ∂P) - (∫ ω, (X.drift * (s : ℝ) - X.X s ω) ∂P))) := by
  have : IsProbabilityMeasure P := X.isProbability
  have hd : 0 < X.drift := drift_pos X hX hBV
  let g : ℝ → ℝ := fun y => ∑ i : Fin N, c i * Real.exp (((i : ℕ) + 1 : ℝ) * y)
  let Δ : ℝ → ℝ := fun y => F y - g y
  have hlim_sum : Tendsto (fun h : ℝ => ∑ i : Fin N, |c i| * Real.exp (((i : ℕ) + 1 : ℝ) * Z_max) *
      |(Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1) / h - X.ψ ((i : ℕ) + 1 : ℝ)|) (𝓝[>] 0) (𝓝 0) := by
    suffices h : Tendsto (fun h : ℝ => ∑ i : Fin N, |c i| * Real.exp (((i : ℕ) + 1 : ℝ) * Z_max) *
        |(Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1) / h - X.ψ ((i : ℕ) + 1 : ℝ)|)
        (𝓝[>] 0) (𝓝 (∑ _i : Fin N, (0 : ℝ))) by simpa using h
    refine tendsto_finsetSum Finset.univ fun i _ => ?_
    have hd_exp : HasDerivAt (fun h : ℝ => Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)))
        (Real.exp ((0 : ℝ) * X.ψ ((i : ℕ) + 1 : ℝ)) * ((1 : ℝ) * X.ψ ((i : ℕ) + 1 : ℝ))) 0 :=
      (Real.hasDerivAt_exp _).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).mul_const _)
    rw [zero_mul, Real.exp_zero, one_mul, one_mul] at hd_exp
    rw [hasDerivAt_iff_tendsto_slope] at hd_exp
    have hsl : Tendsto (fun h : ℝ => (Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1) / h - X.ψ ((i : ℕ) + 1 : ℝ))
        (𝓝[>] 0) (𝓝 0) := by
      have h1 := (hd_exp.mono_left (nhdsGT_le_nhdsNE 0)).sub (tendsto_const_nhds (x := X.ψ ((i : ℕ) + 1 : ℝ)))
      rw [sub_self] at h1
      refine h1.congr' (Eventually.of_forall fun h => ?_)
      simp [slope_def_field]
    simpa using tendsto_const_nhds.mul hsl.abs
  have hev := (tendsto_order.mp hlim_sum).2 ε₁ hε₁
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨h₀, hh₀_pos, hh₀⟩ := hev
  refine ⟨h₀, hh₀_pos, ?_⟩
  intro s t hst h_le_T h_lt_h₀ h z_clip
  have hh_pos : 0 < h := sub_pos.mpr (show (s : ℝ) < (t : ℝ) from hst)
  have hsum_small : ∑ i : Fin N, |c i| * Real.exp (((i : ℕ) + 1 : ℝ) * Z_max) *
      |(Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1) / h - X.ψ ((i : ℕ) + 1 : ℝ)| ≤ ε₁ :=
    le_of_lt (hh₀ (by rw [Real.dist_eq, sub_zero, abs_of_pos hh_pos]; exact h_lt_h₀) (mem_Ioi.mpr hh_pos))
  set E := E_surv X x D s
  have hE_meas : MeasurableSet E := (𝓕.le t) _ (E_surv_measurable_gt X x hD hst)
  have hz_meas : Measurable z_clip :=
    ((measurable_const.max (((measurable_const.add (X_measurable X s)).sub
      ((DPlus_measurable_gt hD hst).mono (𝓕.le t) le_rfl)))).min measurable_const)
  have hz_mem : ∀ ω, z_clip ω ∈ Icc (0 : ℝ) Z_max := fun ω =>
    ⟨le_min (le_max_left _ _) hZ, min_le_right _ _⟩
  have hF_step_int : Integrable (fun ω => E.indicator (fun ω => F (z_clip ω + (X.X t ω - X.X s ω))) ω) P := by
    refine (integrable_const (max (|B₀|) 1)).mono'
      ((hF_mono.measurable.comp (hz_meas.add ((X_measurable X t).sub (X_measurable X s)))).indicator hE_meas).aestronglyMeasurable ?_
    filter_upwards with ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω, Real.norm_eq_abs, abs_of_nonneg (hF_nn _)]
      exact le_trans (hF_bdd _) (le_trans (le_abs_self B₀) (le_max_left _ _))
    · rw [Set.indicator_of_notMem hω, norm_zero]; positivity
  have hF_base_int : Integrable (fun ω => E.indicator (fun ω => F (z_clip ω)) ω) P := by
    refine (integrable_const (max (|B₀|) 1)).mono'
      ((hF_mono.measurable.comp hz_meas).indicator hE_meas).aestronglyMeasurable ?_
    filter_upwards with ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω, Real.norm_eq_abs, abs_of_nonneg (hF_nn _)]
      exact le_trans (hF_bdd _) (le_trans (le_abs_self B₀) (le_max_left _ _))
    · rw [Set.indicator_of_notMem hω, norm_zero]; positivity
  have hexp_term_int : ∀ (i : Fin N) (Y : Ω → ℝ), Measurable Y → (∀ᵐ ω ∂P, Y ω ≤ Z_max + X.drift * T) →
      Integrable (fun ω => E.indicator (fun ω => c i * Real.exp (((i : ℕ) + 1 : ℝ) * Y ω)) ω) P := by
    intro i Y hYm hYb
    refine (integrable_const (|c i| * Real.exp (((i : ℕ) + 1 : ℝ) * (Z_max + X.drift * T)))).mono'
      (((Real.measurable_exp.comp (measurable_const.mul hYm)).const_mul (c i)).indicator hE_meas).aestronglyMeasurable ?_
    filter_upwards [hYb] with ω hωb
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hωb (by positivity))) (abs_nonneg _)
    · rw [Set.indicator_of_notMem hω, norm_zero]; positivity
  have hg_step_int : Integrable (fun ω => E.indicator (fun ω => g (z_clip ω + (X.X t ω - X.X s ω))) ω) P := by
    have heq : (fun ω => E.indicator (fun ω => g (z_clip ω + (X.X t ω - X.X s ω))) ω) =
        fun ω => ∑ i : Fin N, E.indicator (fun ω => c i * Real.exp (((i : ℕ) + 1 : ℝ) * (z_clip ω + (X.X t ω - X.X s ω)))) ω := by
      ext ω; by_cases hω : ω ∈ E <;> simp [g, hω]
    rw [heq]
    refine integrable_finsetSum Finset.univ fun i _ => hexp_term_int i _
      (hz_meas.add ((X_measurable X t).sub (X_measurable X s))) ?_
    filter_upwards [pathBV_ae X hBV] with ω hω
    have h1 := (hz_mem ω).2
    have h2 := hω s t (le_of_lt hst)
    have h3 : X.drift * h ≤ X.drift * T := mul_le_mul_of_nonneg_left h_le_T (le_of_lt hd)
    linarith
  have hg_base_int : Integrable (fun ω => E.indicator (fun ω => g (z_clip ω)) ω) P := by
    have heq : (fun ω => E.indicator (fun ω => g (z_clip ω)) ω) =
        fun ω => ∑ i : Fin N, E.indicator (fun ω => c i * Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω := by
      ext ω; by_cases hω : ω ∈ E <;> simp [g, hω]
    rw [heq]
    refine integrable_finsetSum Finset.univ fun i _ => hexp_term_int i _ hz_meas ?_
    filter_upwards with ω
    have : 0 ≤ X.drift * T := mul_nonneg (le_of_lt hd) (le_of_lt hT)
    linarith [(hz_mem ω).2]
  have hg_diff_bound : ∫ ω, E.indicator (fun ω => g (z_clip ω + (X.X t ω - X.X s ω)) - g (z_clip ω)) ω ∂P ≤
      h * q * (∫ ω, E.indicator (fun ω => F (z_clip ω)) ω ∂P) + h * (ε + 2 * ε₁) := by
    have hind_sub : (fun ω => E.indicator (fun ω => g (z_clip ω + (X.X t ω - X.X s ω)) - g (z_clip ω)) ω) =
        fun ω => ∑ i : Fin N, (c i * (E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * (z_clip ω + (X.X t ω - X.X s ω)))) ω -
          E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω)) := by
      ext ω; by_cases hω : ω ∈ E
      · simp only [Set.indicator_of_mem hω, g, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
      · simp [hω]
    have hexp1_int : ∀ i : Fin N, Integrable (fun ω => E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * (z_clip ω + (X.X t ω - X.X s ω)))) ω) P := by
      intro i
      refine (integrable_const (Real.exp (((i : ℕ) + 1 : ℝ) * (Z_max + X.drift * T)))).mono'
        ((Real.measurable_exp.comp (measurable_const.mul (hz_meas.add ((X_measurable X t).sub (X_measurable X s))))).indicator hE_meas).aestronglyMeasurable ?_
      filter_upwards [pathBV_ae X hBV] with ω hω
      by_cases hE : ω ∈ E
      · rw [Set.indicator_of_mem hE, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr; apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := hω s t (le_of_lt hst)
        have : X.drift * h ≤ X.drift * T := mul_le_mul_of_nonneg_left h_le_T (le_of_lt hd)
        linarith [(hz_mem ω).2]
      · rw [Set.indicator_of_notMem hE, norm_zero]; exact le_of_lt (Real.exp_pos _)
    have hexp0_int : ∀ i : Fin N, Integrable (fun ω => E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω) P := by
      intro i
      refine (integrable_const (Real.exp (((i : ℕ) + 1 : ℝ) * Z_max))).mono'
        ((Real.measurable_exp.comp (measurable_const.mul hz_meas)).indicator hE_meas).aestronglyMeasurable ?_
      filter_upwards with ω
      by_cases hE : ω ∈ E
      · rw [Set.indicator_of_mem hE, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hz_mem ω).2 (by positivity))
      · rw [Set.indicator_of_notMem hE, norm_zero]; exact le_of_lt (Real.exp_pos _)
    have hterm_i : ∀ i : Fin N, Integrable
        (fun ω => c i * (E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * (z_clip ω + (X.X t ω - X.X s ω)))) ω -
          E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω)) P :=
      fun i => ((hexp1_int i).sub (hexp0_int i)).const_mul (c i)
    rw [hind_sub, integral_finsetSum Finset.univ (fun i _ => hterm_i i)]
    have hsum_eval : (∑ i : Fin N, ∫ ω, c i * (E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * (z_clip ω + (X.X t ω - X.X s ω)))) ω -
          E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω) ∂P) =
        ∑ i : Fin N, c i * (∫ ω, E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω ∂P) *
          (Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1) := by
      apply Finset.sum_congr rfl; intro i _
      rw [integral_const_mul, integral_sub (hexp1_int i) (hexp0_int i),
          exp_step_expectation X hBV x Z_max ((i : ℕ) + 1 : ℝ) hZ (by positivity) hD hst]
      ring
    rw [hsum_eval]
    have hlin_approx : (∑ i : Fin N, c i * (∫ ω, E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω ∂P) *
          (Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1)) -
        h * (∑ i : Fin N, c i * (∫ ω, E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω ∂P) *
          X.ψ ((i : ℕ) + 1 : ℝ)) ≤ h * ε₁ := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      calc ∑ i : Fin N, (c i * (∫ ω, E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω ∂P) *
              (Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1) -
            h * (c i * (∫ ω, E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω ∂P) * X.ψ ((i : ℕ) + 1 : ℝ)))
          ≤ ∑ i : Fin N, h * (|c i| * Real.exp (((i : ℕ) + 1 : ℝ) * Z_max) *
              |(Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1) / h - X.ψ ((i : ℕ) + 1 : ℝ)|) := by
            apply Finset.sum_le_sum; intro i _
            set I_i := ∫ ω, E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω ∂P
            have hIi_nn : 0 ≤ I_i := integral_nonneg fun ω => by
              by_cases hE : ω ∈ E
              · rw [Set.indicator_of_mem hE]; exact le_of_lt (Real.exp_pos _)
              · rw [Set.indicator_of_notMem hE]; exact le_rfl
            have hIi_le : I_i ≤ Real.exp (((i : ℕ) + 1 : ℝ) * Z_max) := by
              calc I_i ≤ ∫ _, Real.exp (((i : ℕ) + 1 : ℝ) * Z_max) ∂P := by
                    apply integral_mono (hexp0_int i) (integrable_const _)
                    intro ω; dsimp only
                    by_cases hE : ω ∈ E
                    · rw [Set.indicator_of_mem hE]; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hz_mem ω).2 (by positivity))
                    · rw [Set.indicator_of_notMem hE]; exact le_of_lt (Real.exp_pos _)
                _ = Real.exp (((i : ℕ) + 1 : ℝ) * Z_max) := by simp
            have hrew_i : c i * I_i * (Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1) - h * (c i * I_i * X.ψ ((i : ℕ) + 1 : ℝ)) =
                h * (c i * I_i * ((Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1) / h - X.ψ ((i : ℕ) + 1 : ℝ))) := by
              field_simp [ne_of_gt hh_pos]
            rw [hrew_i]
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hh_pos)
            calc c i * I_i * ((Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1) / h - X.ψ ((i : ℕ) + 1 : ℝ))
                ≤ |c i * I_i * ((Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1) / h - X.ψ ((i : ℕ) + 1 : ℝ))| := le_abs_self _
              _ = |c i| * I_i * |(Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1) / h - X.ψ ((i : ℕ) + 1 : ℝ)| := by
                  rw [abs_mul, abs_mul, abs_of_nonneg hIi_nn]
              _ ≤ |c i| * Real.exp (((i : ℕ) + 1 : ℝ) * Z_max) *
                    |(Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1) / h - X.ψ ((i : ℕ) + 1 : ℝ)| :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIi_le (abs_nonneg _)) (abs_nonneg _)
        _ = h * ∑ i : Fin N, |c i| * Real.exp (((i : ℕ) + 1 : ℝ) * Z_max) *
              |(Real.exp (h * X.ψ ((i : ℕ) + 1 : ℝ)) - 1) / h - X.ψ ((i : ℕ) + 1 : ℝ)| := (Finset.mul_sum _ _ _).symm
        _ ≤ h * ε₁ := mul_le_mul_of_nonneg_left hsum_small (le_of_lt hh_pos)
    have hpsi_bound : ∑ i : Fin N, c i * (∫ ω, E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω ∂P) *
          X.ψ ((i : ℕ) + 1 : ℝ) ≤
        q * (∫ ω, E.indicator (fun ω => F (z_clip ω)) ω ∂P) + (ε + ε₁) := by
      have hsum_in : (∑ i : Fin N, c i * (∫ ω, E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω ∂P) *
            X.ψ ((i : ℕ) + 1 : ℝ)) =
          ∫ ω, E.indicator (fun ω => ∑ i : Fin N, c i * Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω) * X.ψ ((i : ℕ) + 1 : ℝ)) ω ∂P := by
        have hind_eq : (fun ω => E.indicator (fun ω => ∑ i : Fin N, c i * Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω) * X.ψ ((i : ℕ) + 1 : ℝ)) ω) =
            fun ω => ∑ i : Fin N, (c i * X.ψ ((i : ℕ) + 1 : ℝ)) * E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω := by
          ext ω; by_cases hE : ω ∈ E
          · simp only [Set.indicator_of_mem hE]; apply Finset.sum_congr rfl; intro i _; ring
          · simp [hE]
        rw [hind_eq, integral_finsetSum Finset.univ (fun i _ => (hexp0_int i).const_mul _)]
        apply Finset.sum_congr rfl; intro i _; rw [integral_const_mul]; ring
      rw [hsum_in]
      have hconst_P : ∀ c : ℝ, ∫ _, c ∂P = c := fun c => by simp
      have hpt : ∫ ω, E.indicator (fun ω => ∑ i : Fin N, c i * Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω) * X.ψ ((i : ℕ) + 1 : ℝ)) ω ∂P ≤
          ∫ ω, (q * E.indicator (fun ω => F (z_clip ω)) ω + (ε + ε₁)) ∂P := by
        apply integral_mono
        · have hind_eq : E.indicator (fun ω => ∑ i : Fin N, c i * Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω) * X.ψ ((i : ℕ) + 1 : ℝ)) =
              fun ω => ∑ i : Fin N, (c i * X.ψ ((i : ℕ) + 1 : ℝ)) * E.indicator (fun ω => Real.exp (((i : ℕ) + 1 : ℝ) * z_clip ω)) ω := by
            ext ω; by_cases hE : ω ∈ E
            · simp only [Set.indicator_of_mem hE]; apply Finset.sum_congr rfl; intro i _; ring
            · simp [hE]
          rw [hind_eq]
          exact integrable_finsetSum Finset.univ (fun i _ => (hexp0_int i).const_mul _)
        · exact (hF_base_int.const_mul q).add (integrable_const _)
        · intro ω; dsimp only
          by_cases hE : ω ∈ E
          · rw [Set.indicator_of_mem hE, Set.indicator_of_mem hE]
            have h1 := hF_gen (z_clip ω) (hz_mem ω)
            have h2 := hgen_approx (z_clip ω) (hz_mem ω)
            linarith
          · rw [Set.indicator_of_notMem hE, Set.indicator_of_notMem hE]; linarith
      rw [integral_add (hF_base_int.const_mul q) (integrable_const _), integral_const_mul, hconst_P] at hpt
      exact hpt
    have hmul_psi := mul_le_mul_of_nonneg_left hpsi_bound (le_of_lt hh_pos)
    linarith
  have hΔ_diff_bound : ∫ ω, E.indicator (fun ω => Δ (z_clip ω + (X.X t ω - X.X s ω)) - Δ (z_clip ω)) ω ∂P ≤
      ε₁ * (X.drift * h + ((∫ ω, (X.drift * (t : ℝ) - X.X t ω) ∂P) - (∫ ω, (X.drift * (s : ℝ) - X.X s ω) ∂P))) := by
    have hSt_int := S_integrable X hX hBV t
    have hSs_int := S_integrable X hX hBV s
    have hΔ_int : Integrable (fun ω => E.indicator (fun ω => Δ (z_clip ω + (X.X t ω - X.X s ω)) - Δ (z_clip ω)) ω) P := by
      have heq : (fun ω => E.indicator (fun ω => Δ (z_clip ω + (X.X t ω - X.X s ω)) - Δ (z_clip ω)) ω) =
          fun ω => (E.indicator (fun ω => F (z_clip ω + (X.X t ω - X.X s ω))) ω - E.indicator (fun ω => F (z_clip ω)) ω) -
            (E.indicator (fun ω => g (z_clip ω + (X.X t ω - X.X s ω))) ω - E.indicator (fun ω => g (z_clip ω)) ω) := by
        ext ω; by_cases hE : ω ∈ E <;> simp [Δ, hE]; ring
      rw [heq]; exact (hF_step_int.sub hF_base_int).sub (hg_step_int.sub hg_base_int)
    have hdom_int : Integrable (fun ω => ε₁ * (X.drift * h + ((X.drift * (t : ℝ) - X.X t ω) - (X.drift * (s : ℝ) - X.X s ω)))) P :=
      ((integrable_const _).add (hSt_int.sub hSs_int)).const_mul ε₁
    calc ∫ ω, E.indicator (fun ω => Δ (z_clip ω + (X.X t ω - X.X s ω)) - Δ (z_clip ω)) ω ∂P
        ≤ ∫ ω, ε₁ * (X.drift * h + ((X.drift * (t : ℝ) - X.X t ω) - (X.drift * (s : ℝ) - X.X s ω))) ∂P := by
          apply integral_mono_ae hΔ_int hdom_int
          filter_upwards [pathBV_ae X hBV] with ω hω
          set S_inc := (X.drift * (t : ℝ) - X.X t ω) - (X.drift * (s : ℝ) - X.X s ω)
          have hS_nn : 0 ≤ S_inc := by
            have := hω s t (le_of_lt hst)
            dsimp [S_inc, h] at *; linarith
          by_cases hE : ω ∈ E
          · rw [Set.indicator_of_mem hE]
            have hdh_le : X.drift * h ≤ X.drift * T := mul_le_mul_of_nonneg_left h_le_T (le_of_lt hd)
            have hz_dh_le : z_clip ω + X.drift * h ≤ Z_max + X.drift * T + 1 := by
              linarith [(hz_mem ω).2]
            have hpart_d : |Δ (z_clip ω + X.drift * h) - Δ (z_clip ω)| ≤ ε₁ * (X.drift * h) := by
              have h1 := hΔ_lip (z_clip ω) (z_clip ω + X.drift * h)
                (by linarith [mul_pos hd hh_pos]) hz_dh_le
              simpa [Δ] using h1
            have hinc_eq : z_clip ω + (X.X t ω - X.X s ω) = z_clip ω + X.drift * h - S_inc := by
              dsimp [S_inc, h]; ring
            rw [hinc_eq]
            have hpart_S : |Δ (z_clip ω + X.drift * h - S_inc) - Δ (z_clip ω + X.drift * h)| ≤ ε₁ * S_inc := by
              by_cases hS2 : S_inc ≤ 2
              · have h1 := hΔ_lip (z_clip ω + X.drift * h - S_inc) (z_clip ω + X.drift * h)
                  (by linarith) hz_dh_le
                rw [abs_sub_comm] at h1
                simpa [Δ] using h1
              · push Not at hS2
                have hb1 := hΔ_bdd (z_clip ω + X.drift * h - S_inc) (by linarith)
                have hb2 := hΔ_bdd (z_clip ω + X.drift * h) hz_dh_le
                have htwo : 2 * ε₁ ≤ ε₁ * S_inc := by
                  calc 2 * ε₁ = ε₁ * 2 := mul_comm _ _
                    _ ≤ ε₁ * S_inc := mul_le_mul_of_nonneg_left (le_of_lt hS2) (le_of_lt hε₁)
                rw [abs_le]
                exact ⟨by linarith [(abs_le.mp hb1).1, (abs_le.mp hb2).2],
                       by linarith [(abs_le.mp hb1).2, (abs_le.mp hb2).1]⟩
            have htri : Δ (z_clip ω + X.drift * h - S_inc) - Δ (z_clip ω) ≤
                |Δ (z_clip ω + X.drift * h - S_inc) - Δ (z_clip ω + X.drift * h)| +
                |Δ (z_clip ω + X.drift * h) - Δ (z_clip ω)| := by
              linarith [le_abs_self (Δ (z_clip ω + X.drift * h - S_inc) - Δ (z_clip ω + X.drift * h)),
                        le_abs_self (Δ (z_clip ω + X.drift * h) - Δ (z_clip ω))]
            linarith
          · rw [Set.indicator_of_notMem hE]
            exact mul_nonneg (le_of_lt hε₁) (add_nonneg (mul_nonneg (le_of_lt hd) (le_of_lt hh_pos)) hS_nn)
      _ = ε₁ * (X.drift * h + ((∫ ω, (X.drift * (t : ℝ) - X.X t ω) ∂P) - (∫ ω, (X.drift * (s : ℝ) - X.X s ω) ∂P))) := by
          have hS_diff_int : Integrable (fun ω => (X.drift * (t : ℝ) - X.X t ω) - (X.drift * (s : ℝ) - X.X s ω)) P :=
            hSt_int.sub hSs_int
          have hconst_P : ∀ c : ℝ, ∫ _, c ∂P = c := fun c => by simp
          rw [integral_const_mul, integral_add (integrable_const _) hS_diff_int,
              hconst_P, integral_sub hSt_int hSs_int]
  have hF_diff_eq : (∫ ω, E.indicator (fun ω => F (z_clip ω + (X.X t ω - X.X s ω))) ω ∂P) -
      (∫ ω, E.indicator (fun ω => F (z_clip ω)) ω ∂P) =
      (∫ ω, E.indicator (fun ω => g (z_clip ω + (X.X t ω - X.X s ω)) - g (z_clip ω)) ω ∂P) +
      (∫ ω, E.indicator (fun ω => Δ (z_clip ω + (X.X t ω - X.X s ω)) - Δ (z_clip ω)) ω ∂P) := by
    have hg_ind_sub : Integrable (fun ω => E.indicator (fun ω => g (z_clip ω + (X.X t ω - X.X s ω)) - g (z_clip ω)) ω) P := by
      have : (fun ω => E.indicator (fun ω => g (z_clip ω + (X.X t ω - X.X s ω)) - g (z_clip ω)) ω) =
          fun ω => E.indicator (fun ω => g (z_clip ω + (X.X t ω - X.X s ω))) ω - E.indicator (fun ω => g (z_clip ω)) ω := by
        ext ω; by_cases hE : ω ∈ E <;> simp [hE]
      rw [this]; exact hg_step_int.sub hg_base_int
    have hΔ_ind_sub : Integrable (fun ω => E.indicator (fun ω => Δ (z_clip ω + (X.X t ω - X.X s ω)) - Δ (z_clip ω)) ω) P := by
      have : (fun ω => E.indicator (fun ω => Δ (z_clip ω + (X.X t ω - X.X s ω)) - Δ (z_clip ω)) ω) =
          fun ω => (E.indicator (fun ω => F (z_clip ω + (X.X t ω - X.X s ω))) ω - E.indicator (fun ω => F (z_clip ω)) ω) -
            (E.indicator (fun ω => g (z_clip ω + (X.X t ω - X.X s ω))) ω - E.indicator (fun ω => g (z_clip ω)) ω) := by
        ext ω; by_cases hE : ω ∈ E <;> simp [Δ, hE]; ring
      rw [this]; exact (hF_step_int.sub hF_base_int).sub (hg_step_int.sub hg_base_int)
    rw [← integral_sub hF_step_int hF_base_int, ← integral_add hg_ind_sub hΔ_ind_sub]
    apply integral_congr_ae; filter_upwards with ω
    by_cases hE : ω ∈ E <;> simp [Δ, hE]; ring
  set IF0 := ∫ ω, E.indicator (fun ω => F (z_clip ω)) ω ∂P
  set IF1 := ∫ ω, E.indicator (fun ω => F (z_clip ω + (X.X t ω - X.X s ω))) ω ∂P
  have hIF0_nn : 0 ≤ IF0 := integral_nonneg fun ω => by
    by_cases hE : ω ∈ E
    · rw [Set.indicator_of_mem hE]; exact hF_nn _
    · rw [Set.indicator_of_notMem hE]; exact le_rfl
  have hexp_le1 : Real.exp (-(q * h)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [mul_pos hq hh_pos])
  have hexp_pos : 0 ≤ Real.exp (-(q * h)) := le_of_lt (Real.exp_pos _)
  have hrew_disc : Real.exp (-(q * h)) * IF1 - IF0 =
      Real.exp (-(q * h)) * (IF1 - IF0) - (1 - Real.exp (-(q * h))) * IF0 := by ring
  rw [hrew_disc, hF_diff_eq]
  have hdisc_coeff : Real.exp (-(q * h)) * (h * q) - (1 - Real.exp (-(q * h))) ≤ 0 := by
    have h1 : Real.exp (-(q * h)) * (1 + q * h) ≤ Real.exp (-(q * h)) * Real.exp (q * h) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (q * h)]) hexp_pos
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h1
    linarith
  have hcoeff_IF0 : (Real.exp (-(q * h)) * (h * q) - (1 - Real.exp (-(q * h)))) * IF0 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hdisc_coeff hIF0_nn
  have hscale_err : Real.exp (-(q * h)) * (h * (ε + 2 * ε₁) +
      ε₁ * (X.drift * h + ((∫ ω, (X.drift * (t : ℝ) - X.X t ω) ∂P) - (∫ ω, (X.drift * (s : ℝ) - X.X s ω) ∂P)))) ≤
      1 * (h * (ε + 2 * ε₁) +
      ε₁ * (X.drift * h + ((∫ ω, (X.drift * (t : ℝ) - X.X t ω) ∂P) - (∫ ω, (X.drift * (s : ℝ) - X.X s ω) ∂P)))) := by
    apply mul_le_mul_of_nonneg_right hexp_le1
    have hS_mono : ∫ ω, (X.drift * (s : ℝ) - X.X s ω) ∂P ≤ ∫ ω, (X.drift * (t : ℝ) - X.X t ω) ∂P := by
      apply integral_mono_ae (S_integrable X hX hBV s) (S_integrable X hX hBV t)
      filter_upwards [X_sub_le_drift_mul_ae X hBV (le_of_lt hst)] with ω hω
      linarith
    have : 0 ≤ h * (ε + 2 * ε₁) := by positivity
    have : 0 ≤ X.drift * h := by positivity
    exact add_nonneg (by positivity) (mul_nonneg (le_of_lt hε₁) (by linarith))
  have hstep_mul := mul_le_mul_of_nonneg_left (add_le_add hg_diff_bound hΔ_diff_bound) hexp_pos
  linarith

/-! ### Section 6: Zero-horizon case, dyadic grid telescoping, and main proof -/

private lemma zero_horizon_bound (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    {w : ℝ → ℝ} {C : ℝ≥0∞}
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    {x : ℝ} (hxc : ENNReal.ofReal x ≤ C)
    {D : ℝ≥0 → Ω → ℝ} (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have : IsProbabilityMeasure P := X.isProbability
  have hpt : ∀ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ≤ ENNReal.ofReal (w x) := by
    intro ω
    have hset : paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ) = {(0 : ℝ)} := by
      ext t; simp only [paymentTimes, mem_inter_iff, Set.mem_ofPred_eq, mem_Iic, mem_singleton_iff]
      constructor
      · rintro ⟨⟨ht0, _⟩, ht1⟩; linarith
      · rintro rfl; exact ⟨⟨le_rfl, Or.inl rfl⟩, le_rfl⟩
    rw [hset]
    have hcongr : ∫⁻ t in {(0 : ℝ)}, ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) =
        ∫⁻ _ in {(0 : ℝ)}, (1 : ℝ≥0∞) ∂(dividendMeasure D ω) := by
      apply setLIntegral_congr_fun (measurableSet_singleton 0)
      intro t ht; rw [mem_singleton_iff.mp ht]; simp
    rw [hcongr, setLIntegral_const, one_mul, dividendMeasure_singleton_zero hD.1.1 ω]
    apply ENNReal.ofReal_le_ofReal
    have hj := hjump ω 0 (Or.inl rfl)
    have hadm := hD.1.2 ω 0 (Or.inl rfl)
    have hU0 : riskProcess X x D 0 ω = x := by
      unfold riskProcess; rw [X.X_zero ω, hD.1.1.1 ω]; ring
    rw [hU0, hD.1.1.1 ω, sub_zero] at hj hadm
    have hrem_nn : 0 ≤ w (x - rightLimit D 0 ω) := by
      have hd0_nn : 0 ≤ rightLimit D 0 ω := by
        rw [← hD.1.1.1 ω]; exact D_le_DPlus hD.1.1 0 ω
      have hle_C : ENNReal.ofReal (x - rightLimit D 0 ω) ≤ C :=
        le_trans (ENNReal.ofReal_le_ofReal (by linarith)) hxc
      rw [← wExt_eq_of_le (w := w) hle_C]
      exact wExt_nonneg hw_cont hw0 hw_neg hw_smooth hw_grad _
    unfold DPlus; linarith
  calc (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P)
      ≤ ∫⁻ _, ENNReal.ofReal (w x) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (w x) := by simp

private lemma UPlus_le_Z_max {X : SpectrallyNegativeLevy P 𝓕} {x : ℝ} {C : ℝ≥0∞}
    {D : ℝ≥0 → Ω → ℝ} (hD : IsAdmissibleLe X x C D) (hxc : ENNReal.ofReal x ≤ C)
    {T : ℝ} (_hT : 0 ≤ T) (hd : 0 < X.drift)
    {ω : Ω} (hω : PathBV X ω) {t : ℝ≥0} (ht : (t : ℝ) ≤ T) :
    UPlus X x D t ω ≤ (if C = ⊤ then x + X.drift * T + 1 else C.toReal) := by
  have hU_le : UPlus X x D t ω ≤ riskProcess X x D t ω := by
    unfold UPlus riskProcess
    linarith [D_le_DPlus hD.1.1 t ω]
  split_ifs with htop
  · have hX_le : X.X t ω ≤ X.drift * T := by
      have h1 := hω 0 t zero_le
      rw [X.X_zero ω, sub_zero, NNReal.coe_zero, sub_zero] at h1
      exact le_trans h1 (mul_le_mul_of_nonneg_left ht (le_of_lt hd))
    have hD_nn : 0 ≤ D t ω := D_nonneg hD.1.1 t ω
    unfold riskProcess at hU_le
    linarith
  · rcases eq_or_lt_of_le (zero_le : 0 ≤ t) with h0 | hpos
    · rw [← h0] at hU_le ⊢
      have hU0 : riskProcess X x D 0 ω = x := by
        unfold riskProcess; rw [X.X_zero ω, hD.1.1.1 ω]; ring
      rw [hU0] at hU_le
      exact le_trans hU_le ((ENNReal.ofReal_le_iff_le_toReal htop).mp hxc)
    · have hle_C := hD.2 ω t hpos
      by_cases hneg : riskProcess X x D t ω ≤ 0
      · exact le_trans hU_le (le_trans hneg ENNReal.toReal_nonneg)
      · exact le_trans hU_le ((ENNReal.ofReal_le_iff_le_toReal htop).mp hle_C)

private lemma setLIntegral_Iic_grid_le {μ : Measure ℝ} {f : ℝ → ℝ≥0∞} {A : Set ℝ}
    (hA : A ⊆ Ici (0 : ℝ)) {h : ℝ} (_hh : 0 ≤ h) (n : ℕ) :
    ∫⁻ t in A ∩ Iic ((n : ℝ) * h), f t ∂μ ≤
      (∫⁻ t in A ∩ {(0 : ℝ)}, f t ∂μ) +
        ∑ j ∈ Finset.range n, ∫⁻ t in A ∩ Ioc ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h), f t ∂μ := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, Finset.range_zero, Finset.sum_empty, add_zero]
    have hsub : A ∩ Iic (0 : ℝ) ⊆ A ∩ {(0 : ℝ)} := by
      intro t ht; exact ⟨ht.1, mem_singleton_iff.mpr (le_antisymm ht.2 (hA ht.1))⟩
    exact lintegral_mono_set hsub
  | succ n ih =>
    have hsub : A ∩ Iic (((n + 1 : ℕ) : ℝ) * h) ⊆
        (A ∩ Iic ((n : ℝ) * h)) ∪ (A ∩ Ioc ((n : ℝ) * h) (((n + 1 : ℕ) : ℝ) * h)) := by
      intro t ht
      by_cases hle : t ≤ (n : ℝ) * h
      · exact Or.inl ⟨ht.1, hle⟩
      · exact Or.inr ⟨ht.1, not_le.mp hle, ht.2⟩
    calc ∫⁻ t in A ∩ Iic (((n + 1 : ℕ) : ℝ) * h), f t ∂μ
        ≤ ∫⁻ t in (A ∩ Iic ((n : ℝ) * h)) ∪ (A ∩ Ioc ((n : ℝ) * h) (((n + 1 : ℕ) : ℝ) * h)), f t ∂μ :=
          lintegral_mono_set hsub
      _ ≤ (∫⁻ t in A ∩ Iic ((n : ℝ) * h), f t ∂μ) +
            (∫⁻ t in A ∩ Ioc ((n : ℝ) * h) (((n + 1 : ℕ) : ℝ) * h), f t ∂μ) :=
          lintegral_union_le _ _ _
      _ ≤ ((∫⁻ t in A ∩ {(0 : ℝ)}, f t ∂μ) +
            ∑ j ∈ Finset.range n, ∫⁻ t in A ∩ Ioc ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h), f t ∂μ) +
            (∫⁻ t in A ∩ Ioc ((n : ℝ) * h) (((n + 1 : ℕ) : ℝ) * h), f t ∂μ) :=
          add_le_add ih le_rfl
      _ = (∫⁻ t in A ∩ {(0 : ℝ)}, f t ∂μ) +
            ∑ j ∈ Finset.range (n + 1), ∫⁻ t in A ∩ Ioc ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h), f t ∂μ := by
          rw [Finset.sum_range_succ, add_assoc]

private lemma dyadic_grid_pathwise_bound (X : SpectrallyNegativeLevy P 𝓕)
    {q x Z_max T : ℝ} (hq : 0 < q) (_hx : 0 ≤ x) (hZ : 0 ≤ Z_max) (hxZ : x ≤ Z_max)
    (hT : 0 < T) (hd : 0 < X.drift)
    {D : ℝ≥0 → Ω → ℝ} (hD : IsAdmissible X x D)
    {F : ℝ → ℝ} (hF_nn : ∀ y, 0 ≤ F y)
    (hF_grad : ∀ u v, 0 ≤ u → u ≤ v → v ≤ Z_max + X.drift * T + 1 → v - u ≤ F v - F u)
    {n : ℕ} (hn : 0 < n) {ω : Ω} (hω : PathBV X ω)
    (hUZ : ∀ t : ℝ≥0, (t : ℝ) ≤ T → UPlus X x D t ω ≤ Z_max) :
    let h := T / (n : ℝ)
    let t_pt : ℕ → ℝ≥0 := fun j => ⟨(j : ℝ) * h, by positivity⟩
    let z_clip : ℕ → Ω → ℝ := fun j ω' => min (max 0 (UPlus X x D (t_pt j) ω')) Z_max
    let R_cell : ℕ → Ω → ℝ := fun j ω' =>
      (E_surv X x D (t_pt j) \ E_surv X x D (t_pt (j + 1))).indicator
        (fun ω'' => min (Z_max + X.drift * T) (max 0 (D (ruinTime X x D ω'').toNNReal ω'' - D (t_pt j) ω''))) ω'
    let Ψ := F x + (∑ j ∈ Finset.range n,
      (Real.exp (-(q * (t_pt (j + 1) : ℝ))) *
          (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω' + (X.X (t_pt (j + 1)) ω' - X.X (t_pt j) ω'))) ω -
        Real.exp (-(q * (t_pt j : ℝ))) *
          (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω')) ω)) +
      ∑ j ∈ Finset.range n, R_cell j ω
    0 ≤ Ψ ∧
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ≤
        ENNReal.ofReal (Real.exp (q * h)) * ENNReal.ofReal Ψ := by
  intro h t_pt z_clip R_cell Ψ
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hh_pos : 0 < h := div_pos hT hnR
  have hnh : (n : ℝ) * h = T := mul_div_cancel₀ T (ne_of_gt hnR)
  set σ := ruinTime X x D ω
  set μ := dividendMeasure D ω
  have ht_val : ∀ k : ℕ, (t_pt k : ℝ) = (k : ℝ) * h := fun _ => rfl
  have ht_succ : ∀ k : ℕ, (t_pt (k + 1) : ℝ) = (t_pt k : ℝ) + h := fun k => by
    rw [ht_val, ht_val, Nat.cast_add, Nat.cast_one, add_one_mul]
  have ht_lt_succ : ∀ k : ℕ, t_pt k < t_pt (k + 1) := fun k => by
    rw [← NNReal.coe_lt_coe, ht_succ]; linarith
  have hA_sub : paymentTimes σ ⊆ Ici (0 : ℝ) := fun t ht => ht.1
  have hgrid := setLIntegral_Iic_grid_le (μ := μ)
    (f := fun t => ENNReal.ofReal (Real.exp (-(q * t)))) hA_sub (le_of_lt hh_pos) n
  rw [hnh] at hgrid
  have h0_inter : paymentTimes σ ∩ {(0 : ℝ)} = {(0 : ℝ)} :=
    inter_eq_right.mpr (fun t ht => by rw [mem_singleton_iff.mp ht]; exact ⟨le_rfl, Or.inl rfl⟩)
  rw [h0_inter] at hgrid
  have h0_val : ∫⁻ t in {(0 : ℝ)}, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ ≤
      ENNReal.ofReal (Real.exp (q * h)) * ENNReal.ofReal (DPlus D 0 ω) := by
    have hcongr : ∫⁻ t in {(0 : ℝ)}, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ =
        ∫⁻ _ in {(0 : ℝ)}, (1 : ℝ≥0∞) ∂μ := by
      apply setLIntegral_congr_fun (measurableSet_singleton 0)
      intro t ht; rw [mem_singleton_iff.mp ht]; simp
    rw [hcongr, setLIntegral_const, one_mul, dividendMeasure_singleton_zero hD.1 ω]
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (q * h)) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (le_of_lt (mul_pos hq hh_pos)))
    calc ENNReal.ofReal (DPlus D 0 ω) = 1 * ENNReal.ofReal (DPlus D 0 ω) := (one_mul _).symm
      _ ≤ ENNReal.ofReal (Real.exp (q * h)) * ENNReal.ofReal (DPlus D 0 ω) :=
          mul_le_mul_of_nonneg_right h1 zero_le
  let V : ℕ → ℝ := fun j =>
    Real.exp (-(q * (t_pt j : ℝ))) * (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω')) ω
  let δ_cash : ℕ → ℝ := fun j =>
    (μ (paymentTimes σ ∩ Ioc ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h))).toReal
  have hcell_lt_top : ∀ j < n, μ (paymentTimes σ ∩ Ioc ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h)) < ⊤ := by
    intro j _
    refine lt_of_le_of_lt (measure_mono inter_subset_right) ?_
    change μ (Ioc (t_pt j : ℝ) (t_pt (j + 1) : ℝ)) < ⊤
    rw [dividendMeasure_Ioc hD.1 ω]
    exact ENNReal.ofReal_lt_top
  have hcell_disc : ∀ j ∈ Finset.range n,
      ∫⁻ t in paymentTimes σ ∩ Ioc ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ ≤
      ENNReal.ofReal (Real.exp (q * h)) *
        ENNReal.ofReal (Real.exp (-(q * (t_pt (j + 1) : ℝ))) * δ_cash j) := by
    intro j hj
    set S_j := paymentTimes σ ∩ Ioc ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h)
    calc ∫⁻ t in S_j, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ
        ≤ ∫⁻ _ in S_j, ENNReal.ofReal (Real.exp (q * h) * Real.exp (-(q * (t_pt (j + 1) : ℝ)))) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem ((measurableSet_Ici.inter ((measurableSet_singleton 0).union
            (measurableSet_lt ENNReal.measurable_ofReal measurable_const))).inter measurableSet_Ioc)] with t ht
          apply ENNReal.ofReal_le_ofReal
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have ht_gt : (j : ℝ) * h < t := ht.2.1
          rw [ht_succ, ht_val]
          have hq_lt : q * ((j : ℝ) * h) < q * t := mul_lt_mul_of_pos_left ht_gt hq
          have hring : q * h + -(q * ((j : ℝ) * h + h)) = -(q * ((j : ℝ) * h)) := by ring
          rw [hring]; linarith
      _ = ENNReal.ofReal (Real.exp (q * h) * Real.exp (-(q * (t_pt (j + 1) : ℝ)))) * μ S_j := by
          rw [setLIntegral_const]
      _ = ENNReal.ofReal (Real.exp (q * h)) *
            ENNReal.ofReal (Real.exp (-(q * (t_pt (j + 1) : ℝ))) * δ_cash j) := by
          rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)), mul_assoc,
              ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)),
              ENNReal.ofReal_toReal (ne_of_lt (hcell_lt_top j (Finset.mem_range.mp hj)))]
  have hstep_real : ∀ j ∈ Finset.range n,
      Real.exp (-(q * (t_pt (j + 1) : ℝ))) * δ_cash j + V (j + 1) - V j ≤
        (Real.exp (-(q * (t_pt (j + 1) : ℝ))) *
            (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω' + (X.X (t_pt (j + 1)) ω' - X.X (t_pt j) ω'))) ω -
          V j) + R_cell j ω := by
    intro j hj
    have hj_lt : j < n := Finset.mem_range.mp hj
    have ht1_le_T : (t_pt (j + 1) : ℝ) ≤ T := by
      rw [ht_val, ← hnh]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hj_lt) (le_of_lt hh_pos)
    have htj_le_T : (t_pt j : ℝ) ≤ T := le_trans (by rw [ht_succ]; linarith) ht1_le_T
    by_cases hEj : ω ∈ E_surv X x D (t_pt j)
    · have hU_nn_j : 0 ≤ UPlus X x D (t_pt j) ω :=
        UPlus_nonneg_of_admissible hD ω (t_pt j) (Or.inr hEj)
      have hz_eq_j : z_clip j ω = UPlus X x D (t_pt j) ω := by
        dsimp [z_clip]
        rw [max_eq_right hU_nn_j, min_eq_left (hUZ (t_pt j) htj_le_T)]
      by_cases hEj1 : ω ∈ E_surv X x D (t_pt (j + 1))
      · -- Survival at j+1
        have hnot_diff : ω ∉ E_surv X x D (t_pt j) \ E_surv X x D (t_pt (j + 1)) := fun hc => hc.2 hEj1
        have hR0 : R_cell j ω = 0 := Set.indicator_of_notMem hnot_diff _
        have hU_nn_j1 : 0 ≤ UPlus X x D (t_pt (j + 1)) ω :=
          UPlus_nonneg_of_admissible hD ω (t_pt (j + 1)) (Or.inr hEj1)
        have hz_eq_j1 : z_clip (j + 1) ω = UPlus X x D (t_pt (j + 1)) ω := by
          dsimp [z_clip]
          rw [max_eq_right hU_nn_j1, min_eq_left (hUZ (t_pt (j + 1)) ht1_le_T)]
        have hS_eq : paymentTimes σ ∩ Ioc ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) =
            Ioc (t_pt j : ℝ) (t_pt (j + 1) : ℝ) := by
          apply inter_eq_right.mpr
          intro t ht
          refine ⟨le_trans (t_pt j).coe_nonneg (le_of_lt ht.1), Or.inr ?_⟩
          have ht_le : ENNReal.ofReal t ≤ (t_pt (j + 1) : ℝ≥0∞) := by
            rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal ht.2
          exact lt_of_le_of_lt ht_le hEj1
        have hδ_eq : δ_cash j = DPlus D (t_pt (j + 1)) ω - DPlus D (t_pt j) ω := by
          dsimp [δ_cash]; rw [hS_eq, dividendMeasure_Ioc hD.1 ω]
          exact ENNReal.toReal_ofReal (sub_nonneg.mpr (by
            apply le_ciInf; intro s
            exact ciInf_le (DPlus_bddBelow hD.1 (t_pt j) ω) ⟨s.1, lt_trans (ht_lt_succ j) s.2⟩))
        have hδ_nn : 0 ≤ δ_cash j := by
          dsimp [δ_cash]; exact ENNReal.toReal_nonneg
        have hrel : z_clip j ω + (X.X (t_pt (j + 1)) ω - X.X (t_pt j) ω) = z_clip (j + 1) ω + δ_cash j := by
          rw [hz_eq_j, hz_eq_j1, hδ_eq]; unfold UPlus; ring
        have htop_le : z_clip (j + 1) ω + δ_cash j ≤ Z_max + X.drift * T + 1 := by
          rw [← hrel, hz_eq_j]
          have h1 := hUZ (t_pt j) htj_le_T
          have h2 := hω (t_pt j) (t_pt (j + 1)) (le_of_lt (ht_lt_succ j))
          have h3 : (t_pt (j + 1) : ℝ) - (t_pt j : ℝ) ≤ T := by linarith [(t_pt j).coe_nonneg]
          have h4 : X.drift * ((t_pt (j + 1) : ℝ) - (t_pt j : ℝ)) ≤ X.drift * T :=
            mul_le_mul_of_nonneg_left h3 (le_of_lt hd)
          linarith
        have hgrad := hF_grad (z_clip (j + 1) ω) (z_clip (j + 1) ω + δ_cash j)
          (by rw [hz_eq_j1]; exact hU_nn_j1) (by linarith) htop_le
        simp only [V, Set.indicator_of_mem hEj1, Set.indicator_of_mem hEj, hR0, hrel]
        have hmul := mul_le_mul_of_nonneg_left hgrad (le_of_lt (Real.exp_pos (-(q * (t_pt (j + 1) : ℝ)))))
        linarith
      · -- Ruin in (t_pt j, t_pt (j+1)]
        have hmem_diff : ω ∈ E_surv X x D (t_pt j) \ E_surv X x D (t_pt (j + 1)) := ⟨hEj, hEj1⟩
        have hσ_le : σ ≤ (t_pt (j + 1) : ℝ≥0∞) := not_lt.mp hEj1
        have hσ_ne_top : σ ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hσ_le ENNReal.coe_lt_top)
        set σ_nn := σ.toNNReal
        have hσ_coe : (σ_nn : ℝ≥0∞) = σ := ENNReal.coe_toNNReal hσ_ne_top
        have hσ_gt_j : t_pt j < σ_nn := ENNReal.coe_lt_coe.mp (hσ_coe.symm ▸ hEj)
        have hσ_pos : 0 < σ_nn := lt_of_le_of_lt zero_le hσ_gt_j
        have hσ_le_j1 : σ_nn ≤ t_pt (j + 1) := ENNReal.coe_le_coe.mp (hσ_coe.symm ▸ hσ_le)
        have hS_sub : paymentTimes σ ∩ Ioc ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) ⊆
            Ioo (t_pt j : ℝ) (σ_nn : ℝ) := by
          intro t ht
          have ht_gt0 : 0 < t := lt_of_le_of_lt (by positivity) ht.2.1
          have ht_lt_σ : ENNReal.ofReal t < σ := ht.1.2.resolve_left (ne_of_gt ht_gt0)
          rw [← hσ_coe, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff (NNReal.coe_pos.mpr hσ_pos)] at ht_lt_σ
          exact ⟨ht.2.1, ht_lt_σ⟩
        have hδ_le1 : δ_cash j ≤ D σ_nn ω - DPlus D (t_pt j) ω := by
          dsimp [δ_cash]
          have h1 := le_trans (measure_mono hS_sub) (dividendMeasure_Ioo_le hD.1 ω (t_pt j) σ_nn hσ_pos)
          exact ENNReal.toReal_le_of_le_ofReal (by
            have : DPlus D (t_pt j) ω ≤ D σ_nn ω := by
              set m_mid : ℝ≥0 := ⟨((t_pt j : ℝ) + (σ_nn : ℝ)) / 2, by positivity⟩
              have hm1 : t_pt j < m_mid := by
                change (t_pt j : ℝ) < ((t_pt j : ℝ) + (σ_nn : ℝ)) / 2
                linarith [show (t_pt j : ℝ) < (σ_nn : ℝ) from hσ_gt_j]
              have hm2 : m_mid ≤ σ_nn := by
                change ((t_pt j : ℝ) + (σ_nn : ℝ)) / 2 ≤ (σ_nn : ℝ)
                linarith [show (t_pt j : ℝ) < (σ_nn : ℝ) from hσ_gt_j]
              exact le_trans (ciInf_le (DPlus_bddBelow hD.1 _ ω) ⟨m_mid, hm1⟩) (hD.1.2.1 ω hm2)
            linarith) h1
        have hdiff_bdd : D σ_nn ω - DPlus D (t_pt j) ω ≤ Z_max + X.drift * T := by
          have hbound_s : ∀ s : ℝ≥0, t_pt j ≤ s → s < σ_nn → D s ω - DPlus D (t_pt j) ω ≤ Z_max + X.drift * T := by
            intro s hjs hsσ
            have hUs_nn : 0 ≤ riskProcess X x D s ω :=
              riskProcess_nonneg_of_lt_ruin (by
                change (s : ℝ≥0∞) < σ
                rw [← hσ_coe, ENNReal.coe_lt_coe]; exact hsσ)
            have hid : D s ω - DPlus D (t_pt j) ω =
                UPlus X x D (t_pt j) ω - riskProcess X x D s ω + (X.X s ω - X.X (t_pt j) ω) := by
              unfold UPlus riskProcess; ring
            have hX_inc : X.X s ω - X.X (t_pt j) ω ≤ X.drift * T := by
              calc X.X s ω - X.X (t_pt j) ω ≤ X.drift * ((s : ℝ) - (t_pt j : ℝ)) := hω (t_pt j) s hjs
                _ ≤ X.drift * T := mul_le_mul_of_nonneg_left
                    (by linarith [(t_pt j).coe_nonneg, show (s : ℝ) ≤ T from le_trans (le_of_lt hsσ) (le_trans hσ_le_j1 ht1_le_T)])
                    (le_of_lt hd)
            linarith [hUZ (t_pt j) htj_le_T]
          let sn : ℕ → ℝ≥0 := fun k => max (t_pt j) ⟨(σ_nn : ℝ) - ((σ_nn : ℝ) - (t_pt j : ℝ)) / (k + 2 : ℝ), by
            have hlt_R : (t_pt j : ℝ) < (σ_nn : ℝ) := hσ_gt_j
            have h2_ge : (1 : ℝ) ≤ (k : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
            have hdiv_le : ((σ_nn : ℝ) - (t_pt j : ℝ)) / (k + 2 : ℝ) ≤ (σ_nn : ℝ) - (t_pt j : ℝ) :=
              div_le_self (by linarith) h2_ge
            linarith [(t_pt j).coe_nonneg]⟩
          have hsn_lt : ∀ k, sn k < σ_nn := by
            intro k; apply max_lt hσ_gt_j
            change (σ_nn : ℝ) - ((σ_nn : ℝ) - (t_pt j : ℝ)) / (k + 2 : ℝ) < (σ_nn : ℝ)
            have hpos_diff : 0 < ((σ_nn : ℝ) - (t_pt j : ℝ)) / (k + 2 : ℝ) :=
              div_pos (sub_pos.mpr hσ_gt_j) (by positivity)
            linarith
          have hsn_tend : Tendsto sn atTop (𝓝 σ_nn) := by
            have h1 : Tendsto (fun k : ℕ => ((σ_nn : ℝ) - (t_pt j : ℝ)) * (1 / ((k + 1 : ℕ) + 1 : ℝ))) atTop (𝓝 (((σ_nn : ℝ) - (t_pt j : ℝ)) * 0)) :=
              tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1))
            rw [mul_zero] at h1
            have h2 : Tendsto (fun k : ℕ => (σ_nn : ℝ) - ((σ_nn : ℝ) - (t_pt j : ℝ)) / (k + 2 : ℝ)) atTop (𝓝 (σ_nn : ℝ)) := by
              simpa [sub_zero] using (tendsto_const_nhds (x := (σ_nn : ℝ))).sub (h1.congr fun k => by push_cast; ring)
            have h3 : Tendsto (fun k : ℕ => max (t_pt j : ℝ) ((σ_nn : ℝ) - ((σ_nn : ℝ) - (t_pt j : ℝ)) / (k + 2 : ℝ)))
                atTop (𝓝 (max (t_pt j : ℝ) (σ_nn : ℝ))) := tendsto_const_nhds.max h2
            rw [max_eq_right (le_of_lt (show (t_pt j : ℝ) < (σ_nn : ℝ) from hσ_gt_j)), ← NNReal.tendsto_coe] at *
            refine h3.congr fun k => ?_
            set b_k : ℝ≥0 := ⟨(σ_nn : ℝ) - ((σ_nn : ℝ) - (t_pt j : ℝ)) / (k + 2 : ℝ), by
              have hlt_R : (t_pt j : ℝ) < (σ_nn : ℝ) := hσ_gt_j
              have h2_ge : (1 : ℝ) ≤ (k : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
              have hdiv_le : ((σ_nn : ℝ) - (t_pt j : ℝ)) / (k + 2 : ℝ) ≤ (σ_nn : ℝ) - (t_pt j : ℝ) :=
                div_le_self (by linarith) h2_ge
              linarith [(t_pt j).coe_nonneg]⟩
            change max (t_pt j : ℝ) (b_k : ℝ) = ((max (t_pt j) b_k : ℝ≥0) : ℝ)
            cases le_total (t_pt j) b_k with
            | inl h => rw [max_eq_right h, max_eq_right (NNReal.coe_le_coe.mpr h)]
            | inr h => rw [max_eq_left h, max_eq_left (NNReal.coe_le_coe.mpr h)]
          have hD_tend : Tendsto (fun k => D (sn k) ω - DPlus D (t_pt j) ω) atTop (𝓝 (D σ_nn ω - DPlus D (t_pt j) ω)) := by
            refine ((hD.1.2.2.1 ω σ_nn).tendsto.comp ?_).sub tendsto_const_nhds
            exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hsn_tend
              (Eventually.of_forall fun k => le_of_lt (hsn_lt k))
          exact le_of_tendsto hD_tend (Eventually.of_forall fun k => hbound_s (sn k) (le_max_left _ _) (hsn_lt k))
        have hδ_le_R : δ_cash j ≤ R_cell j ω := by
          dsimp only [R_cell]
          rw [Set.indicator_of_mem hmem_diff]
          apply le_min
          · exact le_trans hδ_le1 hdiff_bdd
          · refine le_trans ?_ (le_max_right 0 _)
            linarith [hδ_le1, D_le_DPlus hD.1 (t_pt j) ω]
        have hexp_le1 : Real.exp (-(q * (t_pt (j + 1) : ℝ))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by linarith [mul_nonneg (le_of_lt hq) (t_pt (j + 1)).coe_nonneg])
        have hδ_nn : 0 ≤ δ_cash j := ENNReal.toReal_nonneg
        have hprod_le : Real.exp (-(q * (t_pt (j + 1) : ℝ))) * δ_cash j ≤ R_cell j ω := by
          calc Real.exp (-(q * (t_pt (j + 1) : ℝ))) * δ_cash j ≤ 1 * δ_cash j := mul_le_mul_of_nonneg_right hexp_le1 hδ_nn
            _ = δ_cash j := one_mul _
            _ ≤ R_cell j ω := hδ_le_R
        simp only [V, Set.indicator_of_notMem hEj1, Set.indicator_of_mem hEj, mul_zero]
        have hF1_nn : 0 ≤ Real.exp (-(q * (t_pt (j + 1) : ℝ))) * F (z_clip j ω + (X.X (t_pt (j + 1)) ω - X.X (t_pt j) ω)) :=
          mul_nonneg (le_of_lt (Real.exp_pos _)) (hF_nn _)
        linarith
    · -- Already ruined at or before t_pt j
      have hEj1 : ω ∉ E_surv X x D (t_pt (j + 1)) :=
        fun hc => hEj (lt_trans (ENNReal.coe_lt_coe.mpr (ht_lt_succ j)) hc)
      have hS_empty : paymentTimes σ ∩ Ioc ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) = ∅ := by
        ext t; simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
        rintro ⟨ht1, ht2⟩
        have ht_pos : 0 < t := lt_of_le_of_lt (by positivity) ht2.1
        have ht_lt : ENNReal.ofReal t < σ := ht1.2.resolve_left (ne_of_gt ht_pos)
        have hle_t : (t_pt j : ℝ≥0∞) < ENNReal.ofReal t := by
          rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff ht_pos]
          exact ht2.1
        exact hEj (lt_trans hle_t ht_lt)
      have hδ0 : δ_cash j = 0 := by dsimp [δ_cash]; rw [hS_empty]; simp
      have hR_nn : 0 ≤ R_cell j ω := by
        dsimp [R_cell]; by_cases hc : ω ∈ E_surv X x D (t_pt j) \ E_surv X x D (t_pt (j + 1))
        · rw [Set.indicator_of_mem hc]; exact le_min (by positivity) (le_max_left _ _)
        · rw [Set.indicator_of_notMem hc]
      simp only [V, hδ0, Set.indicator_of_notMem hEj, Set.indicator_of_notMem hEj1,
        mul_zero, add_zero, zero_add, sub_self]
      exact hR_nn
  have h0_bound : DPlus D 0 ω + V 0 ≤ F x := by
    have hadm0 : 0 ≤ UPlus X x D 0 ω := UPlus_nonneg_of_admissible hD ω 0 (Or.inl rfl)
    have hU0_eq : UPlus X x D 0 ω = x - DPlus D 0 ω := by
      unfold UPlus; rw [X.X_zero ω]; ring
    have hd0_nn : 0 ≤ DPlus D 0 ω := by rw [← hD.1.1 ω]; exact D_le_DPlus hD.1 0 ω
    have hx_le_M : x ≤ Z_max + X.drift * T + 1 := by
      have : 0 ≤ X.drift * T := mul_nonneg (le_of_lt hd) (le_of_lt hT)
      linarith
    have hgrad0 := hF_grad (x - DPlus D 0 ω) x (by linarith) (by linarith) hx_le_M
    have ht0 : t_pt 0 = 0 := by ext; change ((0 : ℕ) : ℝ) * h = 0; simp
    dsimp only [V]
    rw [ht0]
    simp only [NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero, one_mul]
    by_cases hE0 : ω ∈ E_surv X x D 0
    · rw [Set.indicator_of_mem hE0]
      have hz0 : z_clip 0 ω = x - DPlus D 0 ω := by
        dsimp [z_clip]; rw [ht0, max_eq_right hadm0, hU0_eq, min_eq_left (by linarith)]
      rw [hz0]; linarith
    · rw [Set.indicator_of_notMem hE0, add_zero]
      linarith [hF_nn (x - DPlus D 0 ω)]
  have hsum_real : DPlus D 0 ω + ∑ j ∈ Finset.range n, Real.exp (-(q * (t_pt (j + 1) : ℝ))) * δ_cash j ≤
      F x + (∑ j ∈ Finset.range n,
        (Real.exp (-(q * (t_pt (j + 1) : ℝ))) *
            (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω' + (X.X (t_pt (j + 1)) ω' - X.X (t_pt j) ω'))) ω -
          V j)) + ∑ j ∈ Finset.range n, R_cell j ω := by
    have h1 := Finset.sum_le_sum hstep_real
    rw [Finset.sum_add_distrib] at h1
    have htel : (∑ j ∈ Finset.range n, (Real.exp (-(q * (t_pt (j + 1) : ℝ))) * δ_cash j + V (j + 1) - V j)) =
        (∑ j ∈ Finset.range n, Real.exp (-(q * (t_pt (j + 1) : ℝ))) * δ_cash j) + (V n - V 0) := by
      have : ∀ j, Real.exp (-(q * (t_pt (j + 1) : ℝ))) * δ_cash j + V (j + 1) - V j =
          Real.exp (-(q * (t_pt (j + 1) : ℝ))) * δ_cash j + (V (j + 1) - V j) := fun _ => by ring
      simp_rw [this, Finset.sum_add_distrib, Finset.sum_range_sub (fun j => V j) n]
    rw [htel] at h1
    have hVn_nn : 0 ≤ V n := by
      dsimp [V]; apply mul_nonneg (le_of_lt (Real.exp_pos _))
      by_cases hnE : ω ∈ E_surv X x D (t_pt n)
      · rw [Set.indicator_of_mem hnE]; exact hF_nn _
      · rw [Set.indicator_of_notMem hnE]
    linarith
  have hd0_nn : 0 ≤ DPlus D 0 ω := by rw [← hD.1.1 ω]; exact D_le_DPlus hD.1 0 ω
  have hsum_nn : ∀ j ∈ Finset.range n, 0 ≤ Real.exp (-(q * (t_pt (j + 1) : ℝ))) * δ_cash j :=
    fun j _ => mul_nonneg (le_of_lt (Real.exp_pos _)) ENNReal.toReal_nonneg
  have hΨ_nn : 0 ≤ Ψ := le_trans (add_nonneg hd0_nn (Finset.sum_nonneg hsum_nn)) hsum_real
  refine ⟨hΨ_nn, ?_⟩
  calc ∫⁻ t in paymentTimes σ ∩ Iic T, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ
      ≤ (∫⁻ t in {(0 : ℝ)}, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) +
          ∑ j ∈ Finset.range n, ∫⁻ t in paymentTimes σ ∩ Ioc ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂μ := hgrid
    _ ≤ ENNReal.ofReal (Real.exp (q * h)) * ENNReal.ofReal (DPlus D 0 ω) +
          ∑ j ∈ Finset.range n, ENNReal.ofReal (Real.exp (q * h)) *
            ENNReal.ofReal (Real.exp (-(q * (t_pt (j + 1) : ℝ))) * δ_cash j) :=
          add_le_add h0_val (Finset.sum_le_sum hcell_disc)
    _ = ENNReal.ofReal (Real.exp (q * h)) *
          (ENNReal.ofReal (DPlus D 0 ω) +
            ∑ j ∈ Finset.range n, ENNReal.ofReal (Real.exp (-(q * (t_pt (j + 1) : ℝ))) * δ_cash j)) := by
          rw [← Finset.mul_sum, mul_add]
    _ = ENNReal.ofReal (Real.exp (q * h)) *
          ENNReal.ofReal (DPlus D 0 ω + ∑ j ∈ Finset.range n, Real.exp (-(q * (t_pt (j + 1) : ℝ))) * δ_cash j) := by
          congr 1
          rw [← ENNReal.ofReal_sum_of_nonneg hsum_nn,
              ← ENNReal.ofReal_add hd0_nn (Finset.sum_nonneg hsum_nn)]
    _ ≤ ENNReal.ofReal (Real.exp (q * h)) * ENNReal.ofReal Ψ :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hsum_real) zero_le

private lemma R_rem_tendsto_zero (X : SpectrallyNegativeLevy P 𝓕)
    {x K_cap T : ℝ} (hK : 0 ≤ K_cap) (hT : 0 < T)
    {D : ℝ≥0 → Ω → ℝ} (hD : IsDividendStrategy 𝓕 D) :
    let R_rem : ℕ → Ω → ℝ := fun k ω =>
      let n : ℕ := 2 ^ k
      let h := T / (n : ℝ)
      let t_pt : ℕ → ℝ≥0 := fun j => ⟨(j : ℝ) * h, by positivity⟩
      ∑ j ∈ Finset.range n,
        (E_surv X x D (t_pt j) \ E_surv X x D (t_pt (j + 1))).indicator
          (fun ω' => min K_cap (max 0 (D (ruinTime X x D ω').toNNReal ω' - D (t_pt j) ω'))) ω
    (∀ k, Integrable (R_rem k) P) ∧
      Tendsto (fun k => ∫ ω, R_rem k ω ∂P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := X.isProbability
  intro R_rem
  have hσ_meas : Measurable (fun ω => (ruinTime X x D ω).toNNReal) :=
    ENNReal.measurable_toNNReal.comp (measurable_ruinTime X x hD)
  have hDσ_meas : Measurable (fun ω => D (ruinTime X x D ω).toNNReal ω) :=
    measurable_D_at_stop hD hσ_meas
  have hR_meas : ∀ k, Measurable (R_rem k) := by
    intro k
    apply Finset.measurable_sum
    intro j _
    set h := T / ((2 ^ k : ℕ) : ℝ)
    have hh_pos : 0 < h := div_pos hT (by positivity)
    set tj : ℝ≥0 := ⟨(j : ℝ) * h, by positivity⟩
    set tj1 : ℝ≥0 := ⟨((j + 1 : ℕ) : ℝ) * h, by positivity⟩
    have hlt : tj < tj1 := by
      change (j : ℝ) * h < ((j + 1 : ℕ) : ℝ) * h
      rw [Nat.cast_add, Nat.cast_one, add_one_mul]; linarith
    have hlt2 : tj1 < tj1 + 1 := lt_add_of_pos_right _ zero_lt_one
    have hEj : MeasurableSet (E_surv X x D tj) := (𝓕.le _) _ (E_surv_measurable_gt X x hD hlt)
    have hEj1 : MeasurableSet (E_surv X x D tj1) := (𝓕.le _) _ (E_surv_measurable_gt X x hD hlt2)
    have hDj : Measurable (D tj) := (hD.2.2.2 tj).mono (𝓕.le tj) le_rfl
    exact (measurable_const.min (measurable_const.max (hDσ_meas.sub hDj))).indicator (hEj.diff hEj1)
  have hR_bdd : ∀ k ω, 0 ≤ R_rem k ω ∧ R_rem k ω ≤ K_cap := by
    intro k ω
    dsimp only [R_rem]
    set n : ℕ := 2 ^ k
    set h := T / (n : ℝ)
    have hh_pos : 0 < h := div_pos hT (by positivity)
    let t_pt : ℕ → ℝ≥0 := fun j => ⟨(j : ℝ) * h, by positivity⟩
    refine ⟨Finset.sum_nonneg fun j _ => ?_, ?_⟩
    · by_cases hm : ω ∈ E_surv X x D (t_pt j) \ E_surv X x D (t_pt (j + 1))
      · rw [Set.indicator_of_mem hm]; exact le_min hK (le_max_left _ _)
      · rw [Set.indicator_of_notMem hm]
    · by_cases hex : ∃ j₀ ∈ Finset.range n, ω ∈ E_surv X x D (t_pt j₀) \ E_surv X x D (t_pt (j₀ + 1))
      · obtain ⟨j₀, hj₀_mem, hj₀⟩ := hex
        rw [Finset.sum_eq_single j₀]
        · rw [Set.indicator_of_mem hj₀]; exact min_le_left _ _
        · intro j _ hne
          apply Set.indicator_of_notMem
          intro hj
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hle : t_pt (j + 1) ≤ t_pt j₀ := by
              change ((j + 1 : ℕ) : ℝ) * h ≤ (j₀ : ℝ) * h
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) (le_of_lt hh_pos)
            exact hj.2 (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr hle) hj₀.1)
          · have hle : t_pt (j₀ + 1) ≤ t_pt j := by
              change ((j₀ + 1 : ℕ) : ℝ) * h ≤ (j : ℝ) * h
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hgt) (le_of_lt hh_pos)
            exact hj₀.2 (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr hle) hj.1)
        · intro hnot; exact absurd hj₀_mem hnot
      · push Not at hex
        have h0 : ∑ j ∈ Finset.range n,
            (E_surv X x D (t_pt j) \ E_surv X x D (t_pt (j + 1))).indicator
              (fun ω' => min K_cap (max 0 (D (ruinTime X x D ω').toNNReal ω' - D (t_pt j) ω'))) ω = 0 :=
          Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem (hex j hj) _
        rw [h0]; exact hK
  have hR_int : ∀ k, Integrable (R_rem k) P := fun k => by
    refine (integrable_const K_cap).mono' (hR_meas k).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hR_bdd k ω).1]
    exact (hR_bdd k ω).2
  refine ⟨hR_int, ?_⟩
  have h0 : (0 : ℝ) = ∫ _, (0 : ℝ) ∂P := by simp
  rw [h0]
  apply tendsto_integral_of_dominated_convergence (fun _ => K_cap)
  · exact fun k => (hR_meas k).aestronglyMeasurable
  · exact integrable_const K_cap
  · intro k; filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hR_bdd k ω).1]; exact (hR_bdd k ω).2
  · filter_upwards with ω
    set σ := ruinTime X x D ω
    by_cases hσ_in : (0 : ℝ≥0∞) < σ ∧ σ ≤ ENNReal.ofReal T
    · have hσ_ne_top : σ ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hσ_in.2 ENNReal.ofReal_lt_top)
      set σ_nn := σ.toNNReal
      have hσ_coe : (σ_nn : ℝ≥0∞) = σ := ENNReal.coe_toNNReal hσ_ne_top
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hcont := hD.2.2.1 ω σ_nn
      rw [Metric.continuousWithinAt_iff] at hcont
      obtain ⟨δ, hδ_pos, hδ⟩ := hcont ε hε
      have htend_mesh : Tendsto (fun k : ℕ => T * (1 / 2 : ℝ) ^ k) atTop (𝓝 (T * 0)) :=
        tendsto_const_nhds.mul
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
      rw [mul_zero] at htend_mesh
      have hev_mesh := (tendsto_order.mp htend_mesh).2 δ hδ_pos
      rw [eventually_atTop] at hev_mesh
      obtain ⟨K₁, hK₁⟩ := hev_mesh
      refine ⟨K₁, fun k hk => ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hR_bdd k ω).1]
      dsimp only [R_rem]
      set n : ℕ := 2 ^ k
      set h := T / (n : ℝ)
      have hh_pos : 0 < h := div_pos hT (by positivity)
      have hh_lt_δ : h < δ := by
        have heq_h : h = T * (1 / 2 : ℝ) ^ k := by
          dsimp [h, n]; rw [one_div, inv_pow, div_eq_mul_inv]; push_cast; rfl
        rw [heq_h]; exact hK₁ k hk
      let t_pt : ℕ → ℝ≥0 := fun j => ⟨(j : ℝ) * h, by positivity⟩
      by_cases hex : ∃ j₀ ∈ Finset.range n, ω ∈ E_surv X x D (t_pt j₀) \ E_surv X x D (t_pt (j₀ + 1))
      · obtain ⟨j₀, hj₀_mem, hj₀⟩ := hex
        rw [Finset.sum_eq_single j₀]
        · rw [Set.indicator_of_mem hj₀]
          have hj₀_lt : t_pt j₀ < σ_nn := ENNReal.coe_lt_coe.mp (hσ_coe.symm ▸ hj₀.1)
          have hj₀1_ge : σ_nn ≤ t_pt (j₀ + 1) := ENNReal.coe_le_coe.mp (hσ_coe.symm ▸ not_lt.mp hj₀.2)
          have hdist : dist (t_pt j₀) σ_nn < δ := by
            rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr (le_of_lt hj₀_lt))), neg_sub]
            have hstep_h : (t_pt (j₀ + 1) : ℝ) - (t_pt j₀ : ℝ) = h := by
              change ((j₀ + 1 : ℕ) : ℝ) * h - (j₀ : ℝ) * h = h; push_cast; ring
            have hle_R : (σ_nn : ℝ) ≤ (t_pt (j₀ + 1) : ℝ) := hj₀1_ge
            linarith
          have hD_close := hδ (le_of_lt hj₀_lt) hdist
          rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hD.2.1 ω (le_of_lt hj₀_lt)))] at hD_close
          exact lt_of_le_of_lt (min_le_right _ _) (max_lt hε hD_close)
        · intro j _ hne
          apply Set.indicator_of_notMem
          intro hj
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hle : t_pt (j + 1) ≤ t_pt j₀ := by
              change ((j + 1 : ℕ) : ℝ) * h ≤ (j₀ : ℝ) * h
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) (le_of_lt hh_pos)
            exact hj.2 (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr hle) hj₀.1)
          · have hle : t_pt (j₀ + 1) ≤ t_pt j := by
              change ((j₀ + 1 : ℕ) : ℝ) * h ≤ (j : ℝ) * h
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hgt) (le_of_lt hh_pos)
            exact hj₀.2 (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr hle) hj.1)
        · intro hnot; exact absurd hj₀_mem hnot
      · push Not at hex
        rw [Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem (hex j hj) _]
        exact hε
    · refine tendsto_const_nhds.congr fun k => ?_
      dsimp only [R_rem]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      apply Set.indicator_of_notMem
      intro hmem
      apply hσ_in
      refine ⟨lt_of_le_of_lt zero_le hmem.1, ?_⟩
      refine le_trans (not_lt.mp hmem.2) ?_
      have hval := @ENNReal.ofReal_coe_nnreal ⟨((j + 1 : ℕ) : ℝ) * (T / ((2 ^ k : ℕ) : ℝ)), by positivity⟩
      rw [← hval]
      apply ENNReal.ofReal_le_ofReal
      have hj_le : ((j + 1 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
      calc ((j + 1 : ℕ) : ℝ) * (T / ((2 ^ k : ℕ) : ℝ))
          ≤ ((2 ^ k : ℕ) : ℝ) * (T / ((2 ^ k : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hj_le (div_nonneg (le_of_lt hT) (by positivity))
        _ = T := mul_div_cancel₀ T (by positivity)

end

end AvramA06Carbon

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  open Filter Topology ProbabilityTheory AvramA06Carbon in
  let _ := hw_nonneg
  rcases eq_or_lt_of_le hT with rfl | hT_pos
  · exact zero_horizon_bound X q hw_cont hw0 hw_neg hw_smooth hw_grad hxc hD hjump
  · have : IsProbabilityMeasure P := X.isProbability
    have hd : 0 < X.drift := drift_pos X hX hBV
    have hwx_nn : 0 ≤ w x := by
      rw [← wExt_eq_of_le (w := w) hxc]
      exact wExt_nonneg hw_cont hw0 hw_neg hw_smooth hw_grad x
    apply ENNReal.le_of_forall_pos_le_add
    intro ε_nn hε_nn _
    set ε_tot : ℝ := (ε_nn : ℝ)
    have hε_tot : 0 < ε_tot := hε_nn
    have hrew_add : ENNReal.ofReal (w x) + (ε_nn : ℝ≥0∞) = ENNReal.ofReal (w x + ε_tot) := by
      rw [ENNReal.ofReal_add hwx_nn (le_of_lt hε_tot), ENNReal.ofReal_coe_nnreal]
    rw [hrew_add]
    set Z_max : ℝ := if C = ⊤ then x + X.drift * T + 1 else C.toReal
    have hxZ : x ≤ Z_max := by
      dsimp [Z_max]; split_ifs with htop
      · have : 0 ≤ X.drift * T := mul_nonneg (le_of_lt hd) hT
        linarith
      · exact (ENNReal.ofReal_le_iff_le_toReal htop).mp hxc
    have hZ0 : 0 ≤ Z_max := le_trans hx hxZ
    have hZC : C ≠ ⊤ → Z_max ≤ C.toReal := fun htop => by simp [Z_max, htop]
    set ε := ε_tot / (2 * (1 + T))
    have hε_pos : 0 < ε := div_pos hε_tot (by positivity)
    obtain ⟨F, B₀, a, ha_pos, hF_zero, _, hF_mono, hF_nn, hF_bdd, hF_diff, hF_deriv_cont,
            hF_grad, hFx_le, hF_gen_full⟩ :=
      exists_smooth_supersolution X hX hBV hq hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
        hx hxc hxZ hZC hT hε_pos
    set ε₂ := ε_tot / 2
    have hε₂_pos : 0 < ε₂ := half_pos hε_tot
    suffices h_F_bound : (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (F x + T * ε + ε₂) by
      refine le_trans h_F_bound (ENNReal.ofReal_le_ofReal ?_)
      have h1 : (1 + T) * ε = ε_tot / 2 := by
        dsimp [ε]
        have hne : (1 + T : ℝ) ≠ 0 := by positivity
        field_simp [hne]
      dsimp only [ε₂]
      linarith
    set S_hor : ℝ≥0 := ⟨T, hT⟩
    set IS_T := ∫ ω, (X.drift * T - X.X S_hor ω) ∂P
    have hIS_T_nn : 0 ≤ IS_T := by
      apply integral_nonneg_of_ae
      filter_upwards [X_le_drift_mul_ae X hBV S_hor] with ω hω
      change 0 ≤ X.drift * T - X.X S_hor ω
      change X.X S_hor ω ≤ X.drift * T at hω
      linarith
    set K_scale := 2 * T + X.drift * T + IS_T + 1
    have hK_scale_pos : 0 < K_scale := by positivity
    set ε₁ := ε₂ / (2 * K_scale)
    have hε₁_pos : 0 < ε₁ := div_pos hε₂_pos (by positivity)
    obtain ⟨N, c, hΔ_bdd, hΔ_lip, hgen_approx⟩ :=
      exists_exp_sum_approx X hBV ha_pos hZ0
        (show Z_max ≤ Z_max + X.drift * T + 1 by linarith [mul_pos hd hT_pos]) hε₁_pos
        hF_zero hF_diff hF_deriv_cont (fun z hz => (hF_gen_full z hz).1)
    obtain ⟨h₀, hh₀_pos, hF_step⟩ :=
      F_step_expectation_bound X hX hBV hq hZ0 hT_pos hε_pos hε₁_pos hD.1.1
        hF_mono hF_nn hF_bdd (fun z hz => (hF_gen_full z hz).2) hΔ_bdd hΔ_lip hgen_approx
    obtain ⟨hR_int, hR_tend⟩ := R_rem_tendsto_zero X (K_cap := Z_max + X.drift * T)
      (by linarith [mul_pos hd hT_pos]) hT_pos hD.1.1
    have hmesh_tend : Tendsto (fun k : ℕ => T / ((2 ^ k : ℕ) : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => T * (1 / 2 : ℝ) ^ k) atTop (𝓝 (T * 0)) :=
        tendsto_const_nhds.mul
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
      rw [mul_zero] at h1
      refine h1.congr fun k => ?_
      rw [one_div, inv_pow, div_eq_mul_inv]; push_cast; rfl
    have hexp_mesh_tend : Tendsto (fun k : ℕ => Real.exp (q * (T / ((2 ^ k : ℕ) : ℝ)))) atTop (𝓝 1) := by
      rw [← Real.exp_zero]
      exact Real.continuous_exp.continuousAt.tendsto.comp (by simpa using tendsto_const_nhds.mul hmesh_tend)
    have hk_bound : ∀ᶠ k : ℕ in atTop,
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (Real.exp (q * (T / ((2 ^ k : ℕ) : ℝ)))) *
          ENNReal.ofReal (F x + T * (ε + 2 * ε₁) + ε₁ * (X.drift * T + IS_T) +
            ∫ ω, (let n : ℕ := 2 ^ k; let h := T / (n : ℝ); let t_pt : ℕ → ℝ≥0 := fun j => ⟨(j : ℝ) * h, by positivity⟩;
              ∑ j ∈ Finset.range n,
                (E_surv X x D (t_pt j) \ E_surv X x D (t_pt (j + 1))).indicator
                  (fun ω' => min (Z_max + X.drift * T) (max 0 (D (ruinTime X x D ω').toNNReal ω' - D (t_pt j) ω'))) ω) ∂P) := by
      filter_upwards [(tendsto_order.mp hmesh_tend).2 h₀ hh₀_pos] with k hk_h₀
      set n : ℕ := 2 ^ k
      have hn_pos : 0 < n := pow_pos (by norm_num) k
      set h := T / (n : ℝ)
      have hh_pos : 0 < h := div_pos hT_pos (by positivity)
      have hnh : (n : ℝ) * h = T := mul_div_cancel₀ T (by positivity)
      let t_pt : ℕ → ℝ≥0 := fun j => ⟨(j : ℝ) * h, by positivity⟩
      let z_clip : ℕ → Ω → ℝ := fun j ω' => min (max 0 (UPlus X x D (t_pt j) ω')) Z_max
      let R_k : Ω → ℝ := fun ω => ∑ j ∈ Finset.range n,
        (E_surv X x D (t_pt j) \ E_surv X x D (t_pt (j + 1))).indicator
          (fun ω' => min (Z_max + X.drift * T) (max 0 (D (ruinTime X x D ω').toNNReal ω' - D (t_pt j) ω'))) ω
      let Ψ_k : Ω → ℝ := fun ω =>
        F x + (∑ j ∈ Finset.range n,
          (Real.exp (-(q * (t_pt (j + 1) : ℝ))) *
              (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω' + (X.X (t_pt (j + 1)) ω' - X.X (t_pt j) ω'))) ω -
            Real.exp (-(q * (t_pt j : ℝ))) *
              (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω')) ω)) + R_k ω
      have hcell_int : ∀ j : ℕ,
          Integrable (fun ω => (E_surv X x D (t_pt j)).indicator
            (fun ω' => F (z_clip j ω' + (X.X (t_pt (j + 1)) ω' - X.X (t_pt j) ω'))) ω) P ∧
          Integrable (fun ω => (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω')) ω) P := by
        intro j
        have hlt : t_pt j < t_pt (j + 1) := by
          change (j : ℝ) * h < ((j + 1 : ℕ) : ℝ) * h
          rw [Nat.cast_add, Nat.cast_one, add_one_mul]; linarith
        have hEj_m : MeasurableSet (E_surv X x D (t_pt j)) :=
          (𝓕.le _) _ (E_surv_measurable_gt X x hD.1.1 hlt)
        have hz_m : Measurable (z_clip j) :=
          ((measurable_const.max (((measurable_const.add (X_measurable X _)).sub
            ((DPlus_measurable_gt hD.1.1 hlt).mono (𝓕.le _) le_rfl)))).min measurable_const)
        constructor
        · refine (integrable_const (max (|B₀|) 1)).mono'
            ((hF_mono.measurable.comp (hz_m.add ((X_measurable X _).sub (X_measurable X _)))).indicator hEj_m).aestronglyMeasurable ?_
          filter_upwards with ω
          by_cases hE : ω ∈ E_surv X x D (t_pt j)
          · rw [Set.indicator_of_mem hE, Real.norm_eq_abs, abs_of_nonneg (hF_nn _)]
            exact le_trans (hF_bdd _) (le_trans (le_abs_self B₀) (le_max_left _ _))
          · rw [Set.indicator_of_notMem hE, norm_zero]; positivity
        · refine (integrable_const (max (|B₀|) 1)).mono'
            ((hF_mono.measurable.comp hz_m).indicator hEj_m).aestronglyMeasurable ?_
          filter_upwards with ω
          by_cases hE : ω ∈ E_surv X x D (t_pt j)
          · rw [Set.indicator_of_mem hE, Real.norm_eq_abs, abs_of_nonneg (hF_nn _)]
            exact le_trans (hF_bdd _) (le_trans (le_abs_self B₀) (le_max_left _ _))
          · rw [Set.indicator_of_notMem hE, norm_zero]; positivity
      have hsum_int : Integrable (fun ω => ∑ j ∈ Finset.range n,
          (Real.exp (-(q * (t_pt (j + 1) : ℝ))) *
              (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω' + (X.X (t_pt (j + 1)) ω' - X.X (t_pt j) ω'))) ω -
            Real.exp (-(q * (t_pt j : ℝ))) *
              (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω')) ω)) P :=
        integrable_finsetSum _ fun j _ => ((hcell_int j).1.const_mul _).sub ((hcell_int j).2.const_mul _)
      have hΨ_int : Integrable Ψ_k P :=
        ((integrable_const (F x)).add hsum_int).add (hR_int k)
      have hae_both : ∀ᵐ ω ∂P, 0 ≤ Ψ_k ω ∧
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
          ENNReal.ofReal (Real.exp (q * h)) * ENNReal.ofReal (Ψ_k ω) := by
        filter_upwards [pathBV_ae X hBV] with ω hω
        exact dyadic_grid_pathwise_bound X hq hx hZ0 hxZ hT_pos hd hD.1 hF_nn hF_grad hn_pos hω
          (fun t ht => UPlus_le_Z_max hD hxc hT hd hω ht)
      have hlint : (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (Real.exp (q * h)) * ENNReal.ofReal (∫ ω, Ψ_k ω ∂P) := by
        calc (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
                ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P)
            ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (q * h)) * ENNReal.ofReal (Ψ_k ω) ∂P :=
              lintegral_mono_ae (hae_both.mono fun _ h => h.2)
          _ = ENNReal.ofReal (Real.exp (q * h)) * ∫⁻ ω, ENNReal.ofReal (Ψ_k ω) ∂P :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ = ENNReal.ofReal (Real.exp (q * h)) * ENNReal.ofReal (∫ ω, Ψ_k ω ∂P) := by
              rw [ofReal_integral_eq_lintegral_ofReal hΨ_int (hae_both.mono fun _ h => h.1)]
      refine le_trans hlint (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) zero_le)
      have hΨ_int_eq : ∫ ω, Ψ_k ω ∂P = F x +
          (∑ j ∈ Finset.range n, ∫ ω,
            (Real.exp (-(q * (t_pt (j + 1) : ℝ))) *
                (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω' + (X.X (t_pt (j + 1)) ω' - X.X (t_pt j) ω'))) ω -
              Real.exp (-(q * (t_pt j : ℝ))) *
                (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω')) ω) ∂P) +
          ∫ ω, R_k ω ∂P := by
        have h1_int : Integrable (fun ω => F x + ∑ j ∈ Finset.range n,
            (Real.exp (-(q * (t_pt (j + 1) : ℝ))) *
                (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω' + (X.X (t_pt (j + 1)) ω' - X.X (t_pt j) ω'))) ω -
              Real.exp (-(q * (t_pt j : ℝ))) *
                (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω')) ω)) P :=
          (integrable_const (F x)).add hsum_int
        have hcell_sub_int : ∀ j : ℕ, Integrable (fun ω =>
            Real.exp (-(q * (t_pt (j + 1) : ℝ))) *
                (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω' + (X.X (t_pt (j + 1)) ω' - X.X (t_pt j) ω'))) ω -
              Real.exp (-(q * (t_pt j : ℝ))) *
                (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω')) ω) P :=
          fun j => ((hcell_int j).1.const_mul _).sub ((hcell_int j).2.const_mul _)
        have hconst_P : ∀ c : ℝ, ∫ _, c ∂P = c := fun c => by simp
        dsimp [Ψ_k]
        rw [integral_add h1_int (hR_int k),
            integral_add (integrable_const (F x)) hsum_int,
            hconst_P,
            integral_finsetSum _ (fun j _ => hcell_sub_int j)]
      rw [hΨ_int_eq]
      have hsum_cells : ∑ j ∈ Finset.range n, ∫ ω,
            (Real.exp (-(q * (t_pt (j + 1) : ℝ))) *
                (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω' + (X.X (t_pt (j + 1)) ω' - X.X (t_pt j) ω'))) ω -
              Real.exp (-(q * (t_pt j : ℝ))) *
                (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω')) ω) ∂P ≤
          ∑ j ∈ Finset.range n, (h * (ε + 2 * ε₁) + ε₁ * (X.drift * h +
            ((∫ ω, (X.drift * (t_pt (j + 1) : ℝ) - X.X (t_pt (j + 1)) ω) ∂P) -
             (∫ ω, (X.drift * (t_pt j : ℝ) - X.X (t_pt j) ω) ∂P)))) := by
        apply Finset.sum_le_sum
        intro j _
        have hlt : t_pt j < t_pt (j + 1) := by
          change (j : ℝ) * h < ((j + 1 : ℕ) : ℝ) * h
          rw [Nat.cast_add, Nat.cast_one, add_one_mul]; linarith
        have hstep_h : (t_pt (j + 1) : ℝ) - (t_pt j : ℝ) = h := by
          change ((j + 1 : ℕ) : ℝ) * h - (j : ℝ) * h = h
          push_cast; ring
        have hh_le_T : h ≤ T := by
          rw [← hnh]
          exact le_trans (by linarith) (mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn_pos) (le_of_lt hh_pos))
        have hstep_j := hF_step (t_pt j) (t_pt (j + 1)) hlt (by rw [hstep_h]; exact hh_le_T)
          (by rw [hstep_h]; exact hk_h₀)
        dsimp only at hstep_j
        rw [hstep_h] at hstep_j
        rw [integral_sub ((hcell_int j).1.const_mul _) ((hcell_int j).2.const_mul _),
            integral_const_mul, integral_const_mul]
        have hexp_split : Real.exp (-(q * (t_pt (j + 1) : ℝ))) =
            Real.exp (-(q * (t_pt j : ℝ))) * Real.exp (-(q * h)) := by
          rw [← Real.exp_add]; congr 1; rw [← hstep_h]; ring
        rw [hexp_split]
        have hexp_j_le1 : Real.exp (-(q * (t_pt j : ℝ))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by linarith [mul_nonneg (le_of_lt hq) (t_pt j).coe_nonneg])
        have hexp_j_nn : 0 ≤ Real.exp (-(q * (t_pt j : ℝ))) := le_of_lt (Real.exp_pos _)
        have h1 : Real.exp (-(q * (t_pt j : ℝ))) * Real.exp (-(q * h)) *
              (∫ ω, (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω' + (X.X (t_pt (j + 1)) ω' - X.X (t_pt j) ω'))) ω ∂P) -
            Real.exp (-(q * (t_pt j : ℝ))) *
              (∫ ω, (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω')) ω ∂P) =
            Real.exp (-(q * (t_pt j : ℝ))) *
              (Real.exp (-(q * h)) *
                  (∫ ω, (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω' + (X.X (t_pt (j + 1)) ω' - X.X (t_pt j) ω'))) ω ∂P) -
                (∫ ω, (E_surv X x D (t_pt j)).indicator (fun ω' => F (z_clip j ω')) ω ∂P)) := by ring
        rw [h1]
        have hS_mono : ∫ ω, (X.drift * (t_pt j : ℝ) - X.X (t_pt j) ω) ∂P ≤
            ∫ ω, (X.drift * (t_pt (j + 1) : ℝ) - X.X (t_pt (j + 1)) ω) ∂P := by
          apply integral_mono_ae (S_integrable X hX hBV _) (S_integrable X hX hBV _)
          filter_upwards [X_sub_le_drift_mul_ae X hBV (le_of_lt hlt)] with ω hω
          linarith
        have hrhs_nn : 0 ≤ h * (ε + 2 * ε₁) + ε₁ * (X.drift * h +
            ((∫ ω, (X.drift * (t_pt (j + 1) : ℝ) - X.X (t_pt (j + 1)) ω) ∂P) -
             (∫ ω, (X.drift * (t_pt j : ℝ) - X.X (t_pt j) ω) ∂P))) :=
          add_nonneg (by positivity) (mul_nonneg (le_of_lt hε₁_pos) (add_nonneg (by positivity) (by linarith)))
        calc Real.exp (-(q * (t_pt j : ℝ))) * _
            ≤ Real.exp (-(q * (t_pt j : ℝ))) * (h * (ε + 2 * ε₁) + ε₁ * (X.drift * h +
                ((∫ ω, (X.drift * (t_pt (j + 1) : ℝ) - X.X (t_pt (j + 1)) ω) ∂P) -
                 (∫ ω, (X.drift * (t_pt j : ℝ) - X.X (t_pt j) ω) ∂P)))) :=
              mul_le_mul_of_nonneg_left hstep_j hexp_j_nn
          _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hexp_j_le1 hrhs_nn
          _ = _ := one_mul _
      have htel_rhs : ∑ j ∈ Finset.range n, (h * (ε + 2 * ε₁) + ε₁ * (X.drift * h +
            ((∫ ω, (X.drift * (t_pt (j + 1) : ℝ) - X.X (t_pt (j + 1)) ω) ∂P) -
             (∫ ω, (X.drift * (t_pt j : ℝ) - X.X (t_pt j) ω) ∂P)))) =
          T * (ε + 2 * ε₁) + ε₁ * (X.drift * T + IS_T) := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, Finset.sum_range_sub (fun j => ∫ ω, (X.drift * (t_pt j : ℝ) - X.X (t_pt j) ω) ∂P) n]
        have ht0_eq : t_pt 0 = 0 := by ext; change ((0 : ℕ) : ℝ) * h = 0; simp
        have htn_eq : t_pt n = S_hor := by ext; dsimp [t_pt, S_hor]; exact hnh
        have hS0 : ∫ ω, (X.drift * (t_pt 0 : ℝ) - X.X (t_pt 0) ω) ∂P = 0 := by
          rw [ht0_eq]; simp [X.X_zero]
        have hSn : ∫ ω, (X.drift * (t_pt n : ℝ) - X.X (t_pt n) ω) ∂P = IS_T := by
          rw [htn_eq]; rfl
        rw [hS0, hSn, sub_zero, ← hnh]
        ring
      rw [htel_rhs] at hsum_cells
      linarith
    have hRHS_lim : Tendsto (fun k : ℕ =>
        ENNReal.ofReal (Real.exp (q * (T / ((2 ^ k : ℕ) : ℝ)))) *
          ENNReal.ofReal (F x + T * (ε + 2 * ε₁) + ε₁ * (X.drift * T + IS_T) +
            ∫ ω, (let n : ℕ := 2 ^ k; let h := T / (n : ℝ); let t_pt : ℕ → ℝ≥0 := fun j => ⟨(j : ℝ) * h, by positivity⟩;
              ∑ j ∈ Finset.range n,
                (E_surv X x D (t_pt j) \ E_surv X x D (t_pt (j + 1))).indicator
                  (fun ω' => min (Z_max + X.drift * T) (max 0 (D (ruinTime X x D ω').toNNReal ω' - D (t_pt j) ω'))) ω) ∂P))
        atTop (𝓝 (ENNReal.ofReal 1 * ENNReal.ofReal (F x + T * (ε + 2 * ε₁) + ε₁ * (X.drift * T + IS_T) + 0))) := by
      refine ENNReal.Tendsto.mul
        (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hexp_mesh_tend)
        (Or.inr ENNReal.ofReal_ne_top)
        (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.add hR_tend))
        (Or.inr ENNReal.ofReal_ne_top)
    have hlim_le := ge_of_tendsto hRHS_lim hk_bound
    rw [ENNReal.ofReal_one, one_mul, add_zero] at hlim_le
    refine le_trans hlim_le (ENNReal.ofReal_le_ofReal ?_)
    have hε₁_bound : (2 * T + X.drift * T + IS_T) * ε₁ ≤ ε₂ / 2 := by
      calc (2 * T + X.drift * T + IS_T) * ε₁
          ≤ K_scale * ε₁ := mul_le_mul_of_nonneg_right (by dsimp [K_scale]; linarith) (le_of_lt hε₁_pos)
        _ = ε₂ / 2 := by dsimp [ε₁]; field_simp [ne_of_gt hK_scale_pos]
    linarith
