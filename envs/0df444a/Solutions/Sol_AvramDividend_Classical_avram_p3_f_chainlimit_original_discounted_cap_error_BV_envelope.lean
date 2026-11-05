-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_cap_error_BV_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:22:15.255942+00:00
-- url     : https://prove2.me/submissions/fad6514c-c570-4bbc-aefc-b14d01117391

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_discounted_cap_physical_localTaylor
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_discounted_actual_source_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (hSlope : C ≠ ⊤ → deriv w C.toReal = 1)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      ∀ (n : ℕ) (u : ℕ → ℝ≥0)
        (hGrid : ∀ i, i < n → u i ≤ u (i + 1))
        (hStartCap : ∀ i, i < n → C ≠ ⊤ →
          x + X.X (u i) ω - rightLimit D (u i) ω ≤ C.toReal)
        (hTaylor : ∀ i, i < n → C ≠ ⊤ →
          C.toReal < x + X.X (u (i + 1)) ω - rightLimit D (u i) ω →
          |w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
            w C.toReal -
            deriv w C.toReal *
              (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω - C.toReal)| ≤
          ε * |x + X.X (u (i + 1)) ω - rightLimit D (u i) ω - C.toReal|),
        let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
        let κ : ℕ → ℝ := fun i =>
          let b := x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
          if C = ⊤ then 0
          else if b ≤ C.toReal then 0
          else w C.toReal + (b - C.toReal) - w b
        |∑ i ∈ Finset.range n, e i * κ i| ≤
          ε * (|X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
            (R (u n) - R (u 0)) +
            (J (u n) - J (u 0))) := by
  filter_upwards
    [avram_p3_f_chainlimit_original_discounted_actual_source_variation X hBV,
      avram_p3_f_chainlimit_original_raw_J_monotone X hBV]
      with ω hVar hMono
  intro J R n u hGrid hStartCap hTaylor e κ
  have hjmono : ∀ i, i < n →
      J (u i) ≤ J (u (i + 1)) := by
    intro i hi
    exact hMono (u i) (u (i + 1)) (hGrid i hi)
  have hvariation := hVar n u q hq hGrid hjmono
  have hcap :=
    avram_p3_f_chainlimit_original_discounted_cap_physical_localTaylor
      X x C hC hxc w V hVtop hVfinite D hD u n q hq
      hSlope ε hε ω hStartCap hTaylor
  change
    |∑ i ∈ Finset.range n, e i * κ i| ≤
      ε * (∑ i ∈ Finset.range n,
        e i * |X.X (u (i + 1)) ω - X.X (u i) ω|) at hcap
  change
    (∑ i ∈ Finset.range n,
      e i * |X.X (u (i + 1)) ω - X.X (u i) ω|) ≤
      |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
        (R (u n) - R (u 0)) +
        (J (u n) - J (u 0)) at hvariation
  exact hcap.trans (mul_le_mul_of_nonneg_left hvariation hε)
