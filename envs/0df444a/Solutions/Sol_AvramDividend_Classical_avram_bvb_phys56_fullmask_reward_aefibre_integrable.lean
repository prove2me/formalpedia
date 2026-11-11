-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys56_fullmask_reward_aefibre_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:27:52.133221+00:00
-- url     : https://prove2.me/submissions/cb2e4490-bee5-45a5-998e-f9ec78a0bee5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys55_fullmask_reward_marked_predictable
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys44_original_cap_reward_bounded_below_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_all_borel_band_count_finite_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- A bounded original marked reward with finite negative-jump support is fibrewise integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let J : ℕ → Ω → ℝ := fun n ω => ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
    ∀ n, ∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ => H n ((p.1, ω), p.2)) (NX ω) := by
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
    if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
       (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
       0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
  let J : ℕ → Ω → ℝ := fun n ω => ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
  change ∀ n, ∀ᵐ ω ∂P, Integrable
    (fun p : ℝ≥0 × ℝ => H n ((p.1, ω), p.2)) (NX ω)
  have hPred : ∀ n, Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] (H n) :=
    avram_bvb_phys55_fullmask_reward_marked_predictable
      X hBV q hq w C hC hFinite hw_cont hw_neg x D hD T hT hActivity
  have hPredLe : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      have hA' : MeasurableSet A := (𝓕.rightCont.le (⊥ : ℝ≥0)) A hA
      exact (measurableSet_singleton (⊥ : ℝ≥0)).prod hA'
    · intro i A hA
      have hA' : MeasurableSet A := (𝓕.rightCont.le i) A hA
      exact (measurableSet_Ioi : MeasurableSet (Ioi i)).prod hA'
  have hProdLe : (@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) ≤
      (inferInstance : MeasurableSpace ((ℝ≥0 × Ω) × ℝ)) :=
    by
      change (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ) ≤
        (inferInstance : MeasurableSpace (ℝ≥0 × Ω)).prod
          (inferInstance : MeasurableSpace ℝ)
      unfold MeasurableSpace.prod
      exact sup_le_sup (MeasurableSpace.comap_mono hPredLe) le_rfl
  obtain ⟨R, hR, hRw⟩ :=
    avram_bvb_phys44_original_cap_reward_bounded_below_cap
      w hw_cont hw_neg C.toReal ENNReal.toReal_nonneg
  let B : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) (Real.toNNReal T) ×ˢ Iio (0 : ℝ)
  have hB : MeasurableSet B := measurableSet_Ioc.prod measurableSet_Iio
  have hTnn : 0 < Real.toNNReal T := Real.toNNReal_pos.mpr hT
  have hAlmostFinite : ∀ᵐ ω ∂P, (NX ω) B < ⊤ := by
    simpa only [NX, B] using
      (avram_wave4_04a_bv_actual_intrinsic_all_borel_band_count_finite_ae
        X hBV hActivity (Real.toNNReal T) hTnn
        (Iio (0 : ℝ)) measurableSet_Iio)
  intro n
  filter_upwards [hAlmostFinite] with ω hω
  let f : ℝ≥0 × ℝ → ℝ := fun p => H n ((p.1, ω), p.2)
  have hReorder : Measurable (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) := by fun_prop
  have hf : Measurable f := (hPred n).mono hProdLe le_rfl |>.comp hReorder
  have hPoint : ∀ p ∈ B, ‖f p‖ ≤ 2 * R := by
    intro p hp
    unfold f H
    split_ifs with h
    · have hU0 : 0 ≤ U p.1 ω := h.2.2.2.1
      have hUC : ENNReal.ofReal (U p.1 ω) ≤ C := h.2.2.2.2.1
      have hUcap : U p.1 ω ≤ C.toReal := by
        simpa only [ENNReal.toReal_ofReal hU0] using
          (ENNReal.toReal_mono hFinite hUC)
      have hw1 := hRw (U p.1 ω) hUcap
      have hw2 := hRw (U p.1 ω + p.2) (by linarith [h.2.2.2.2.2])
      have he : 0 ≤ Real.exp (-(q * (p.1 : ℝ))) := le_of_lt (Real.exp_pos _)
      have he1 : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have ht : 0 ≤ (p.1 : ℝ) := NNReal.coe_nonneg p.1
        nlinarith [mul_nonneg hq ht]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg he]
      have hd : |w (U p.1 ω + p.2) - w (U p.1 ω)| ≤ 2 * R := by
        calc
          _ ≤ |w (U p.1 ω + p.2)| + |w (U p.1 ω)| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le (w (U p.1 ω + p.2)) (0 : ℝ) (w (U p.1 ω)))
          _ ≤ R + R := add_le_add hw2 hw1
          _ = 2 * R := by ring
      nlinarith [mul_nonneg (sub_nonneg.mpr he1)
        (abs_nonneg (w (U p.1 ω + p.2) - w (U p.1 ω)))]
    · simp [Real.norm_eq_abs, hR]
  have hSupport : ∀ p ∉ B, f p = 0 := by
    intro p hp
    unfold f H
    split_ifs with h
    · exfalso
      have hd : 0 ≤ δ n := div_nonneg (le_of_lt hT) (by positivity)
      have ht : (p.1 : ℝ) ≤ T := by linarith [h.2.1]
      have htNN : p.1 ≤ Real.toNNReal T := by
        exact_mod_cast (show (p.1 : ℝ) ≤ (Real.toNNReal T : ℝ) by
          simpa [Real.coe_toNNReal _ (le_of_lt hT)] using ht)
      exact hp ⟨⟨h.1, htNN⟩, h.2.2.2.2.2⟩
    · rfl
  have hBound : ∀ᵐ p ∂((NX ω).restrict B), ‖f p‖ ≤ 2 * R := by
    filter_upwards [ae_restrict_mem hB] with p hp
    exact hPoint p hp
  have hIntegrableOn : IntegrableOn f B (NX ω) :=
    Measure.integrableOn_of_bounded hω.ne hf.aestronglyMeasurable hBound
  have hEq : B.indicator f = f := by
    funext p
    by_cases hp : p ∈ B
    · simp [Set.indicator_of_mem hp]
    · simp [Set.indicator_of_notMem hp, hSupport p hp]
  have hI : Integrable (B.indicator f) (NX ω) := (integrable_indicator_iff hB).mpr hIntegrableOn
  change Integrable f (NX ω)
  simpa only [hEq] using hI
