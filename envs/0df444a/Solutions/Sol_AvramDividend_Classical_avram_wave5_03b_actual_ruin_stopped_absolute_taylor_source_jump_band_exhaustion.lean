-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_absolute_taylor_source_jump_band_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:28:39.339545+00:00
-- url     : https://prove2.me/submissions/cd4d023e-c9de-492f-9ac5-48f5fbe8c065

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_randomly_stopped_predictable_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
/-- Actual-source nonlinear Taylor absolute jump reward: increasing negative-mark
bands exhaust its full same-path intrinsic jump integral without a Finset. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (B : ℕ → Set ℝ) (hBmeas : ∀ n, MeasurableSet (B n))
    (hBmono : Monotone B)
    (hBcover : ∀ z : ℝ, z < 0 ↔ ∃ n : ℕ, z ∈ B n) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let J : ℝ≥0 → Ω → ℝ := fun q ω =>
      X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {q : ℝ≥0 | 0 < q ∧ J q ω ≠ 0}).map
        (fun q : ℝ≥0 => (q, J q ω)))
    ∀ (s t : ℝ≥0) (ω : Ω),
      (⨆ n : ℕ,
        (∫⁻ p : ℝ≥0 × ℝ,
          (if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B n then
            ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω)) =
      (∫⁻ p : ℝ≥0 × ℝ,
        (if s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0 then
          ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0) else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  let J : ℝ≥0 → Ω → ℝ := fun q ω => X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {q : ℝ≥0 | 0 < q ∧ J q ω ≠ 0}).map
      (fun q : ℝ≥0 => (q, J q ω)))
  change ∀ (s t : ℝ≥0) (ω : Ω),
      (⨆ n : ℕ,
        (∫⁻ p : ℝ≥0 × ℝ,
          (if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B n then
            ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω)) =
      (∫⁻ p : ℝ≥0 × ℝ,
        (if s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0 then
          ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω)
  have hzero : (0 : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) Set.univ < ⊤ := by simp
  have hHmeas : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] HS := by
    simpa [HS, H, Y] using
      (avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
        X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
        (0 : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) hzero).1
  have hAbsMeas : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] (fun p => ENNReal.ofReal (|HS p|)) := by
    letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
      (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
    exact ENNReal.measurable_ofReal.comp hHmeas.abs
  have hPredLeProd :
      (𝓕.rightCont.predictable) ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) :=
    measurableSpace_le_predictable_of_measurableSet
      (fun A hA => (measurableSet_singleton (⊥ : ℝ≥0)).prod ((𝓕.rightCont.le ⊥) A hA))
      (fun i A hA => measurableSet_Ioi.prod ((𝓕.rightCont.le i) A hA))
  have hAbsStd : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      ENNReal.ofReal (|HS p|)) :=
    hAbsMeas.mono
      (sup_le_sup (MeasurableSpace.comap_mono hPredLeProd) le_rfl) le_rfl
  intro s t ω
  have hAbsPath : Measurable (fun p : ℝ≥0 × ℝ =>
      ENNReal.ofReal (|HS ((p.1,ω),p.2)|)) :=
    hAbsStd.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  let f : ℕ → (ℝ≥0 × ℝ) → ℝ≥0∞ := fun n p =>
    if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B n then ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0
  have hfMeas (n : ℕ) : Measurable (f n) := by
    have hcond : MeasurableSet {p : ℝ≥0 × ℝ |
        s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B n} := by
      have hf : Measurable (fun p : ℝ≥0 × ℝ => p.1) := measurable_fst
      have hg : Measurable (fun p : ℝ≥0 × ℝ => p.2) := measurable_snd
      exact (measurableSet_Ioi.preimage hf).inter
        ((measurableSet_Iic.preimage hf).inter ((hBmeas n).preimage hg))
    simpa [f] using Measurable.ite hcond hAbsPath measurable_const
  have hfMono : Monotone f := by
    intro n m hnm p
    by_cases hn : s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B n
    · have hm : s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B m := ⟨hn.1, hn.2.1, hBmono hnm hn.2.2⟩
      simp [f, hn, hm]
    · simp [f, hn]
  have hSup (p : ℝ≥0 × ℝ) : (⨆ n : ℕ, f n p) =
      if s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0 then
        ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0 := by
    apply le_antisymm
    · apply iSup_le
      intro n
      by_cases hn : s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B n
      · have hz : p.2 < 0 := (hBcover p.2).mpr ⟨n, hn.2.2⟩
        have hfull : s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0 := ⟨hn.1, hn.2.1, hz⟩
        simp [f, hn, hfull]
      · simp [f, hn]
    · by_cases hfull : s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0
      · obtain ⟨n, hn⟩ := (hBcover p.2).mp hfull.2.2
        have hband : s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B n := ⟨hfull.1, hfull.2.1, hn⟩
        calc
          (if s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0 then
            ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) =
              f n p := by simp [f, hfull, hband]
          _ ≤ ⨆ n : ℕ, f n p := le_iSup (fun n => f n p) n
      · simp [hfull]
  calc
    (⨆ n : ℕ,
      (∫⁻ p : ℝ≥0 × ℝ,
        (if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B n then
          ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω))
      = ⨆ n : ℕ, ∫⁻ p : ℝ≥0 × ℝ, f n p ∂NX ω := by rfl
    _ = ∫⁻ p : ℝ≥0 × ℝ, (⨆ n : ℕ, f n p) ∂NX ω :=
      (lintegral_iSup hfMeas hfMono).symm
    _ = ∫⁻ p : ℝ≥0 × ℝ,
        (if s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0 then
          ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω := by
      apply lintegral_congr
      intro p
      exact hSup p
