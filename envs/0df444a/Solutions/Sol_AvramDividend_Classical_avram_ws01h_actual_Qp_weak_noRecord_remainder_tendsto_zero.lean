-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_actual_Qp_weak_noRecord_remainder_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:42:18.865808+00:00
-- url     : https://prove2.me/submissions/d168e846-ed5d-4254-82ac-29760b690d06

import Mathlib.Topology.Order.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_Qp_weak_noRecord_mass_le_exponential_cdf
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_exp_noRecord_CDF_vanishes_at_small_shifted_root

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- The genuine original-path terminal Esscher Qp no-record remainder
vanishes at small rates, without a tilted infinite-path measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q : ℝ) (hφ : 0 < φ) (hq : 0 < q)
    (hroot : X.ψ φ = q)
    (lam : ℝ → ℝ)
    (hlampos : ∀ p : ℝ, 0 < p → 0 < lam p)
    (hshift : ∀ p : ℝ, 0 < p →
      X.ψ (φ + lam p) - q = p)
    (hlam : Tendsto lam (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (0 : ℝ))) (b : ℝ) (hb : 0 ≤ b) :
    Tendsto (fun p : ℝ =>
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * q))))
        {z : Ω × ℝ | 0 ≤ z.2 ∧
          (Real.toNNReal z.2 : ℝ≥0∞) ≤
            twoSidedExitUpTime X b z.1})
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : ℝ≥0∞)) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  let R : ℝ → ℝ≥0∞ := fun p =>
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
        (φ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * q))))
      {z : Ω × ℝ | 0 ≤ z.2 ∧
        (Real.toNNReal z.2 : ℝ≥0∞) ≤
          twoSidedExitUpTime X b z.1}
  have hbd := avram_ws01h_true_exp_noRecord_CDF_vanishes_at_small_shifted_root
    b hb lam hlampos hlam
  have hle : R ≤ᶠ[l] (fun p => expMeasure (lam p) (Iic b)) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    simpa only [R] using
      (avram_ws01h_Qp_weak_noRecord_mass_le_exponential_cdf
        X φ q hφ hq hroot p hp (lam p) (hlampos p hp)
        (hshift p hp) b hb)
  have hlow : (fun _ : ℝ => (0 : ℝ≥0∞)) ≤ᶠ[l] R :=
    Filter.Eventually.of_forall (fun p => bot_le)
  change Tendsto R l (𝓝 (0 : ℝ≥0∞))
  exact Filter.Tendsto.squeeze' tendsto_const_nhds hbd hlow hle
