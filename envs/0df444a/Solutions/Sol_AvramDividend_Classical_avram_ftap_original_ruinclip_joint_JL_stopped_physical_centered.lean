-- Prove2me | solution 1 for AvramDividend.Classical.avram_ftap_original_ruinclip_joint_JL_stopped_physical_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:22:04.044349+00:00
-- url     : https://prove2.me/submissions/62540562-6d33-40b1-a1e3-b5d06529eb3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_ruinclip_allnu_stopped_joint_JL_L1_centered
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_NX_marked_integral_indicator
open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal NNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (Cband u v δ η : ℝ)
    (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband))
    (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (huv : u + δ < v) (hv : v < Cband)
    (hη : 0 < η) (hη1 : η < 1) :
    let T : ℝ≥0 := (n : ℝ≥0)
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then
        (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let Z : ℝ≥0 → Ω → ℝ := MeasureTheory.stoppedProcess X.X
      (fun η => (τ η : WithTop ℝ≥0))
    let SNX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ Z t ω - Function.leftLim (fun r => Z r ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, Z t ω - Function.leftLim (fun r => Z r ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let J : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then GW ((p.1, ω), p.2) else 0) ∂(SNX ω)) -
      (∫ t, ∫ z,
        (if t ≤ ρ ω then GW ((t, ω), z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    let K : Ω → (ℝ≥0 × ℝ) → ℝ := fun ω p =>
      if p.1 ≤ (n : ℝ≥0) ∧ p.2 ∈ Ioo (-1 : ℝ) (-η) then
        Real.exp (-(q * (p.1 : ℝ))) *
          (if Y (p.1, ω) ∈ Icc (u + δ) v then
            deriv w (Y (p.1, ω)) * p.2 else 0)
      else 0
    let L : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then K ω p else 0) ∂(SNX ω)) -
      (∫ t, ∫ z, (if t ≤ ρ ω then K ω (t, z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    Integrable (fun ω => J τ ω + L τ ω) P ∧
      (∫ ω, J τ ω + L τ ω ∂P) = 0 := by
  intro T a Y H HS GW NX Z SNX μT J K L
  have hOld :=
    avram_twoagentA_original_ruinclip_allnu_stopped_joint_JL_L1_centered
      X x D hD w hw_cont hw_neg q hq n τ hτeq hτstop
      Cband u v δ η hwCb hu hδ hδ1 huv hv hη hη1
  have hStop (ω : Ω) (f : ℝ≥0 × ℝ → ℝ)
      (hf : ∀ p, ¬ p.1 ≤ τ ω → f p = 0) :
      (∫ p, f p ∂(SNX ω)) = (∫ p, f p ∂(NX ω)) := by
    rw [(avram_ftap_original_stopped_NX_marked_integral_indicator
      X τ ω).1 f]
    congr 1
    funext p
    by_cases hp : p.1 ≤ τ ω
    · simp [hp]
    · simp [hp, hf p hp]
  have hJPath (ω : Ω) := hStop ω
    (fun p => if p.1 ≤ τ ω then GW ((p.1, ω), p.2) else 0)
    (by intro p hp; simp [hp])
  have hLPath (ω : Ω) := hStop ω
    (fun p => if p.1 ≤ τ ω then K ω p else 0)
    (by intro p hp; simp [hp])
  have hEq (ω : Ω) :
      J τ ω + L τ ω =
        ((∫ p, (if p.1 ≤ τ ω then GW ((p.1, ω), p.2) else 0)
          ∂(NX ω)) -
        (∫ t, ∫ z, (if t ≤ τ ω then GW ((t, ω), z) else 0)
          ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)) +
        ((∫ p, (if p.1 ≤ τ ω then K ω p else 0) ∂(NX ω)) -
        (∫ t, ∫ z, (if t ≤ τ ω then K ω (t, z) else 0)
          ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)) := by
    dsimp [J, L]
    rw [hJPath ω, hLPath ω]
  simp_rw [hEq]
  simpa only using hOld
