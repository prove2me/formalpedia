-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_deterministic_atomic_source_uniform_increment_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:46:28.155507+00:00
-- url     : https://prove2.me/submissions/2ab77dd7-98ad-48ba-9993-2e774d407095

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_AvramDividend_Classical_avram_chat24_atomic_source_uniform_chord_DCT_certificate
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
    Integrable (fun t : ℝ≥0 =>
      if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) * (d * deriv w (Y t)) else 0) μ ∧
    Tendsto (fun n : ℕ =>
      let N : ℕ := n + 1
      let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / (N : ℝ≥0)
      let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
      let U : ℕ → ℝ := fun i => v + f (u i) - K (u i)
      let Z : ℕ → ℝ := fun i => v + f (u (i + 1)) - K (u i)
      ∑ i ∈ Finset.range N, e (i + 1) * (w (Z i) - w (U i)))
      atTop (nhds ((∫ p, if (p.1 : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧
          Y p.1 ∈ Icc a b ∧ p.2 < 0 then
        Real.exp (-(q * (p.1 : ℝ))) * (w (Y p.1 + p.2) - w (Y p.1)) else 0 ∂NX) +
        (∫ t : ℝ≥0, if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b then
          Real.exp (-(q * (t : ℝ))) * (d * deriv w (Y t)) else 0 ∂μ))) := by
  classical
  intro NX μ
  letI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  obtain ⟨n0, L, hL, hAi, hJi, hFm, hGm, hFbound, hGbound, hFlim, hGlim, heq⟩ :=
    avram_chat24_atomic_source_uniform_chord_DCT_certificate
      f K Y v d a b q T hT B hB hBT hd ha hq hf_right hf_left hf_down hK hsum hsource hband hpre w hw
  have hF := tendsto_integral_of_dominated_convergence _ hFm hJi hFbound hFlim
  have hG := tendsto_integral_of_dominated_convergence (fun _ : ℝ≥0 => L * d)
    hGm (integrable_const (L * d)) hGbound hGlim
  refine ⟨hAi, ?_⟩
  simpa only using (hF.add hG).congr' (Filter.EventuallyEq.symm heq)
