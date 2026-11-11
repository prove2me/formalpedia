-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys47_original_fullmask_jump_compensator_clock_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:33:09.245517+00:00
-- url     : https://prove2.me/submissions/90088ce2-8b90-4f65-b3e0-32f41616ce5a

import Mathlib.Probability.Process.Predictable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys41_original_finite_activity_predictable_physical_fibre_L1
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys46_original_finite_cap_inclusive_ruin_fullmask_predictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The strict physical-grid compensator is L1 on the original probability space. -/
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
    let V : ℕ → Ω → ℝ := fun n ω =>
      ∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    ∀ n, Integrable (V n) P := by
  intro δ U H V n
  let Tnn : ℝ≥0 := ⟨T, hT.le⟩
  let E : Set (ℝ≥0 × Ω) := {p |
    0 < p.1 ∧ (p.1 : ℝ) < T - δ n ∧
    (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
    0 ≤ U p.1 p.2 ∧ ENNReal.ofReal (U p.1 p.2) ≤ C}
  have hTime : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => p.1) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    apply measurable_of_Ioi
    intro a
    have hSet : (fun p : ℝ≥0 × Ω => p.1) ⁻¹' Ioi a =
        Ioi a ×ˢ (Set.univ : Set Ω) := by
      ext p
      simp
    rw [hSet]
    exact measurableSet_predictable_Ioi_prod (𝓕 := 𝓕.rightCont)
      (i := a) (s := (Set.univ : Set Ω)) MeasurableSet.univ
  have hCut : MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω | 0 < p.1 ∧ (p.1 : ℝ) < T - δ n} := by
    exact (measurableSet_lt measurable_const hTime).inter
      (measurableSet_lt (measurable_coe_nnreal_real.comp hTime) measurable_const)
  have hBase : MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ (((min (ruinTime X x D p.2) (Tnn : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) ∧
        0 ≤ U p.1 p.2 ∧ ENNReal.ofReal (U p.1 p.2) ≤ C} := by
    simpa only [U, Tnn] using
      (avram_bvb_phys46_original_finite_cap_inclusive_ruin_fullmask_predictable
        X x C hFinite D hD Tnn)
  have hEq : E =
      {p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ (((min (ruinTime X x D p.2) (Tnn : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) ∧
        0 ≤ U p.1 p.2 ∧ ENNReal.ofReal (U p.1 p.2) ≤ C} ∩
      {p : ℝ≥0 × Ω | 0 < p.1 ∧ (p.1 : ℝ) < T - δ n} := by
    ext p
    have hδ : 0 ≤ δ n := div_nonneg hT.le (by positivity)
    have hclock : (p.1 : ℝ) < T - δ n →
        (p.1 : ℝ≥0∞) ≤ (Tnn : ℝ≥0∞) := by
      intro hp
      have hpT : (p.1 : ℝ) < T := lt_of_lt_of_le hp (sub_le_self T hδ)
      exact ENNReal.coe_le_coe.mpr (le_of_lt (by exact_mod_cast hpT))
    have hfinite : min (ruinTime X x D p.2) (Tnn : ℝ≥0∞) ≠ ⊤ := by simp
    have hcoerce := ENNReal.coe_toNNReal hfinite
    constructor
    · rintro ⟨hp0, hpT, hpR, hpZ, hpC⟩
      exact ⟨⟨(by rw [hcoerce]; exact le_min hpR (hclock hpT)), hpZ, hpC⟩,
        hp0, hpT⟩
    · rintro ⟨⟨hpClock, hpZ, hpC⟩, hp0, hpT⟩
      rw [hcoerce] at hpClock
      exact ⟨hp0, hpT, le_trans hpClock (min_le_left _ _), hpZ, hpC⟩
  have hEm : MeasurableSet[𝓕.rightCont.predictable] E := by
    rw [hEq]
    exact hBase.inter hCut
  have hc : 0 ≤ C.toReal := by positivity
  have hRegion : ∀ p ∈ E, U p.1 p.2 ≤ C.toReal := by
    intro p hp
    exact (ENNReal.ofReal_le_iff_le_toReal hFinite).mp hp.2.2.2.2
  have hTnn : (Tnn : ℝ) = T := rfl
  have hPhysical :=
    (avram_bvb_phys41_original_finite_activity_predictable_physical_fibre_L1
      X x D hD.1.1 w hw_cont hw_neg q hq C.toReal hc
      hActivity Tnn E hEm hRegion)
  rw [hTnn] at hPhysical
  simpa only [V, H, E, U, Set.mem_setOf_eq, and_assoc] using hPhysical
