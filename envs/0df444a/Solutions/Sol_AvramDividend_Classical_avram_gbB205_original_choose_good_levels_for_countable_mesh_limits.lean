-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB205_original_choose_good_levels_for_countable_mesh_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:26:40.399492+00:00
-- url     : https://prove2.me/submissions/f68d32bd-0fc3-429b-94e3-f5f99528a7ce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB202_choose_simultaneous_good_stopped_clipping_level
import Theorems.Thm_AvramDividend_Classical_avram_gbB80_original_zerojump_postpayment_ae_countable_discontinuities
import Theorems.Thm_AvramDividend_Classical_avram_gbB204_ae_clipped_uniform_mesh_tendsto_from_null_levels
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Selected original clipping levels give countably simultaneous a.e. mesh convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ → ℕ) (hn : ∀ k, 0 < n k)
    (ρ : ℕ → Ω → ℝ≥0) (q : ℝ) (w : ℝ → ℝ)
    (alo ahi blo bhi : ℝ) (ha : alo < ahi)
    (hSep : ahi < blo) (hb : blo < bhi)
    (hDeriv : ∀ y ∈ Ioo alo bhi, ContinuousAt (deriv w) y) :
    let Y : ℝ≥0 → Ω → ℝ := fun s ω =>
      x + X.X s ω - rightLimit D s ω
    ∃ a : ℝ, a ∈ Ioo alo ahi ∧
    ∃ b : ℝ, b ∈ Ioo blo bhi ∧
      ∀ k : ℕ, ∀ᵐ ω ∂P,
        ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) ((n k : ℕ) : ℝ))),
          Tendsto (fun m : ℕ =>
            let Δ : ℝ≥0 := ((n k : ℕ) : ℝ≥0) /
              ((m + 1 : ℕ) : ℝ≥0)
            (Finset.range (m + 1)).sum (fun i =>
              let s : ℝ≥0 := (i : ℝ≥0) * Δ
              if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ)
              then if (s : ℝ) < (ρ k ω : ℝ) then
                Real.exp (-(q * (s : ℝ))) *
                  (if Y (Real.toNNReal (s : ℝ)) ω ∈ Icc a b
                    then deriv w (Y (Real.toNNReal (s : ℝ)) ω)
                    else 1)
              else 0 else 0)) atTop
            (𝓝 (if t < (ρ k ω : ℝ) then
              Real.exp (-(q * t)) *
                (if Y (Real.toNNReal t) ω ∈ Icc a b
                  then deriv w (Y (Real.toNNReal t) ω)
                  else 1)
              else 0)) := by
  intro Y
  obtain ⟨a, haGood, hARaw⟩ :=
    avram_gbB202_choose_simultaneous_good_stopped_clipping_level
      X x D hD n (fun k _ => (n k : ℝ≥0)) alo ahi ha
  obtain ⟨b, hbGood, hBRaw⟩ :=
    avram_gbB202_choose_simultaneous_good_stopped_clipping_level
      X x D hD n (fun k _ => (n k : ℝ≥0)) blo bhi hb
  have hCount : ∀ᵐ ω ∂P,
      Set.Countable {s : ℝ≥0 |
        ¬ ContinuousAt (fun u : ℝ≥0 => Y u ω) s} := by
    simpa only [Y] using
      (avram_gbB80_original_zerojump_postpayment_ae_countable_discontinuities
        X hν D hD x)
  have hOccA (k : ℕ) : ∀ᵐ ω ∂P,
      volume {t : ℝ | 0 < t ∧ t < ((n k : ℕ) : ℝ) ∧
        Y (Real.toNNReal t) ω = a} = 0 := by
    filter_upwards [hARaw k] with ω hω
    convert hω using 1
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, Y, NNReal.coe_natCast]
    tauto
  have hOccB (k : ℕ) : ∀ᵐ ω ∂P,
      volume {t : ℝ | 0 < t ∧ t < ((n k : ℕ) : ℝ) ∧
        Y (Real.toNNReal t) ω = b} = 0 := by
    filter_upwards [hBRaw k] with ω hω
    convert hω using 1
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, Y, NNReal.coe_natCast]
    tauto
  have hDerivAB : ∀ y ∈ Ioo a b,
      ContinuousAt (deriv w) y := by
    intro y hy
    exact hDeriv y ⟨lt_trans haGood.1 hy.1,
      lt_trans hy.2 hbGood.2⟩
  refine ⟨a, haGood, b, hbGood, ?_⟩
  intro k
  exact avram_gbB204_ae_clipped_uniform_mesh_tendsto_from_null_levels
    Y hCount (n k) (hn k) q w a b (ρ k)
    (hOccA k) (hOccB k) hDerivAB

