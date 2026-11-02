-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_BV_C1_shared_residual_source_and_dividend_prepayment_interface
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:26:59.272466+00:00
-- url     : https://prove2.me/submissions/5bb84dc6-099f-40c5-9098-6264c456d822

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_BV_source_to_controlled_prepayment_increment_balance
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_BV_stopped_C1_compact_deterministic_derivative_ceiling_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A single original-source BV residual controls both the exact
prepayment reserve decomposition and the finite stopped C¹ loss.
The right dividend payment remains a separate chronological update. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw : Monotone w)
    (cap l r : ℝ) (hlr : l < r)
    (hsub : Icc l r ⊆ Ioo 0 cap)
    (hC1 : ContDiffOn ℝ 1 w (Ioo 0 cap)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      (∀ (s t : ℝ≥0), s ≤ t →
        riskProcess X x D t ω - riskProcess X x D s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∫⁻ p,
              (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
              ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim
                    (fun v : ℝ≥0 => X.X v ω) u)))).toReal -
            (R t - R s) - (D t ω - D s ω)) ∧
      (∀ t : ℝ≥0,
        riskProcess X x D t ω - (rightLimit D t ω - D t ω) =
          x + X.X t ω - rightLimit D t ω) ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hcell : ∀ i < n,
          riskProcess X x D (u i) ω ∈ Icc l r ∧
          riskProcess X x D (u i) ω -
            (R (u (i + 1)) - R (u i)) ∈ Icc l r)
        (a : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A)
        (ha : ∀ i, 0 ≤ a i ∧ a i ≤ A),
        0 ≤ (Finset.range n).sum (fun i =>
          a i * (w (riskProcess X x D (u i) ω) -
            w (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))))) ∧
        (Finset.range n).sum (fun i =>
          a i * (w (riskProcess X x D (u i) ω) -
            w (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))))) ≤
          (A * M) * (R (τ ω) - R (u 0)) := by
  obtain ⟨M, hM, hcompact⟩ :=
    avram_wave5_04a_actual_intrinsic_BV_stopped_C1_compact_deterministic_derivative_ceiling_envelope
      X hBV x D w hw cap l r hlr hsub hC1
  refine ⟨M, hM, ?_⟩
  filter_upwards
    [hcompact,
      avram_wave5_04a_actual_intrinsic_BV_source_to_controlled_prepayment_increment_balance
        X hBV x D] with ω hωcompact hωbalance
  obtain ⟨R, hRdef, hRmono, henv⟩ := hωcompact
  obtain ⟨S, hSdef, _hSmono, hbalance, hpayment⟩ := hωbalance
  have hEq : S = R := by
    funext t
    exact (hSdef t).trans (hRdef t).symm
  refine ⟨R, hRdef, hRmono, ?_, hpayment, henv⟩
  intro s t hst
  simpa only [hEq] using hbalance s t hst
