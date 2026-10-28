-- Prove2me | solution 1 for AvramDividend.Classical.chat12_global_exit_identity_yields_eventual_factors
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:15:10.770863+00:00
-- url     : https://prove2.me/submissions/bdc368f8-11d7-4cbe-b1af-4630b5606cd3

import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (a : ℝ) (ha : 0 < a)
    (hIdentity : ∀ (A x : ℝ), 0 < A → 0 ≤ x → x ≤ A →
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : A - x < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : A - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W x / W A)) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W a / W (a + ε))) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W (a - ε) / W a)) := by
  constructor
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have := hIdentity (a + ε) a (by linarith) ha.le (by linarith)
    simpa only [add_sub_cancel_left] using this
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ha] with ε (hε : 0 < ε) hεa
    have := hIdentity a (a - ε) ha (by linarith [hεa.2]) (by linarith)
    simpa only [sub_sub_cancel, neg_sub] using this
