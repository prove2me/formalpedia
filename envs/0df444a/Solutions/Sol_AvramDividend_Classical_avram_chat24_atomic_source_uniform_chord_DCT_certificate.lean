-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_atomic_source_uniform_chord_DCT_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:43:30.651215+00:00
-- url     : https://prove2.me/submissions/7781d143-90d0-4442-ab3a-7d7a48087efe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_chord_jump_branch
import Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_chord_drift_branch
import Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_chord_balance_branch
import Theorems.Thm_AvramDividend_Classical_avram_chat24_compact_chord_cutoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    (f K Y : ℝ≥0 → ℝ) (v d a b q T : ℝ) (hT : 0 ≤ T)
    (B : ℝ≥0) (hB : 0 < B) (hBT : B ≤ (⟨T, hT⟩ : ℝ≥0))
    (hd : 0 < d) (ha : 0 < a) (hq : 0 ≤ q)
    (hf_right : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hf_left : ∀ t : ℝ≥0, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hf_down : ∀ t : ℝ≥0, 0 < t → f t ≤ Function.leftLim f t)
    (hK : Monotone K)
    (hsum : Summable (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ B then Function.leftLim f t - f t else 0))
    (hsource : ∀ t : ℝ≥0, t ≤ B → f t = (t : ℝ) * d -
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then Function.leftLim f u - f u else 0)
    (hband : ∀ t : ℝ≥0, t ≤ B → v + f t - K t ∈ Icc a b)
    (hpre : ∀ t : ℝ≥0, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto (fun s => v + f s - K s) (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 1 w (Ioi 0)) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ f u - Function.leftLim f u ≠ 0}).map
        (fun u : ℝ≥0 => (u, f u - Function.leftLim f u)))
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
    let V : ℕ → ℕ → ℝ := fun n i => v + f (u n i) - K (u n i)
    let m : ℕ → ℕ → ℝ := fun n i =>
      d * h n - (f (u n (i + 1)) - f (u n i))
    let J : ℝ≥0 × ℝ → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0 then
        Real.exp (-(q * (p.1 : ℝ))) * (w (Y p.1 + p.2) - w (Y p.1)) else 0
    let A : ℝ≥0 → ℝ := fun t =>
      if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) * (d * deriv w (Y t)) else 0
    ∃ n0 : ℕ, ∃ L : ℝ, 0 ≤ L ∧
      let F : ℕ → ℝ≥0 × ℝ → ℝ := fun n p => if n0 ≤ n then
        ∑ i ∈ Finset.range (n + 1),
          if u n i < p.1 ∧ p.1 ≤ u n (i + 1) then
            Real.exp (-(q * (u n (i + 1) : ℝ))) *
              ((w (V n i - m n i) - w (V n i)) / m n i) * (-p.2) else 0
        else 0
      let G : ℕ → ℝ≥0 → ℝ := fun n t => if n0 ≤ n then
        ∑ i ∈ Finset.range (n + 1),
          if u n i < t ∧ t ≤ u n (i + 1) then
            Real.exp (-(q * (u n (i + 1) : ℝ))) *
              ((w (V n i + d * h n - m n i) - w (V n i - m n i)) / h n) else 0
        else 0
      let Jdom : ℝ≥0 × ℝ → ℝ := fun p =>
        if 0 < p.1 ∧ p.1 ≤ B ∧ p.2 < 0 then L * (-p.2) else 0
      Integrable A μ ∧ Integrable Jdom NX ∧
      (∀ n, AEStronglyMeasurable (F n) NX) ∧
      (∀ n, AEStronglyMeasurable (G n) μ) ∧
      (∀ n, ∀ᵐ p ∂NX, ‖F n p‖ ≤ Jdom p) ∧
      (∀ n, ∀ᵐ t ∂μ, ‖G n t‖ ≤ L * d) ∧
      (∀ᵐ p ∂NX, Tendsto (fun n => F n p) atTop (nhds (J p))) ∧
      (∀ᵐ t ∂μ, Tendsto (fun n => G n t) atTop (nhds (A t))) ∧
      (∀ᶠ n : ℕ in atTop,
        (∑ i ∈ Finset.range (n + 1),
          Real.exp (-(q * (u n (i + 1) : ℝ))) *
            (w (v + f (u n (i + 1)) - K (u n i)) - w (V n i))) =
          (∫ p, F n p ∂NX) + (∫ t, G n t ∂μ)) := by
  classical
  intro NX μ u h V m J A
  obtain ⟨n0, L, hLip, hsmall⟩ := avram_chat24_compact_chord_cutoff w a b d B ha hw
  obtain ⟨hJD, hFM, hFB, hFL⟩ := avram_chat24_uniform_chord_jump_branch
    f K Y v d a b q T hT B hB hBT hd ha hq
    hf_right hf_left hf_down hK hsum hsource hband hpre w hw n0 L hLip hsmall
  obtain ⟨hAI, hGM, hGB, hGL⟩ := avram_chat24_uniform_chord_drift_branch
    f K Y v d a b q T hT B hB hBT hd ha hq
    hf_right hf_left hf_down hK hsum hsource hband hpre w hw n0 L hLip hsmall
  have hbal := avram_chat24_uniform_chord_balance_branch
    f K Y v d a b q T hT B hB hBT hd ha hq
    hf_right hf_left hf_down hK hsum hsource hband hpre w hw n0
  exact ⟨n0, (L : ℝ), L.property, hAI, hJD, hFM, hGM, hFB, hGB, hFL, hGL, hbal⟩
end
