-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_localised_cap_C1_source_error_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:41:11.241109+00:00
-- url     : https://prove2.me/submissions/0a6ba946-7abf-4365-bd97-a7c2533ee00d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_discounted_cap_physical_localTaylor
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_discounted_actual_source_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
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
    (hSlope : C ≠ ⊤ → deriv w C.toReal = 1) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∀ (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ) (ε : ℕ → ℝ)
        (hGrid : ∀ k i, i < n k → (u k) i ≤ (u k) (i + 1))
        (hε : ∀ k, 0 ≤ ε k)
        (hεlim : Tendsto ε atTop (nhds 0))
        (hStartCap : ∀ k i, i < n k → C ≠ ⊤ →
          x + X.X ((u k) i) ω - rightLimit D ((u k) i) ω ≤ C.toReal)
        (hTaylor : ∀ k i, i < n k → C ≠ ⊤ →
          C.toReal < x + X.X ((u k) (i + 1)) ω -
            rightLimit D ((u k) i) ω →
          |w (x + X.X ((u k) (i + 1)) ω -
            rightLimit D ((u k) i) ω) - w C.toReal -
            deriv w C.toReal *
              (x + X.X ((u k) (i + 1)) ω -
                rightLimit D ((u k) i) ω - C.toReal)| ≤
          ε k * |x + X.X ((u k) (i + 1)) ω -
            rightLimit D ((u k) i) ω - C.toReal|)
        (hSourceBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ k,
          |X.drift| * (((u k) (n k) : ℝ) - ((u k) 0 : ℝ)) +
            (R ((u k) (n k)) - R ((u k) 0)) +
            (J ((u k) (n k)) - J ((u k) 0)) ≤ M),
        let e : ℕ → ℕ → ℝ := fun k i =>
          Real.exp (-(q * ((u k) i : ℝ)))
        let κ : ℕ → ℕ → ℝ := fun k i =>
          let b := x + X.X ((u k) (i + 1)) ω -
            rightLimit D ((u k) i) ω
          if C = ⊤ then 0
          else if b ≤ C.toReal then 0
          else w C.toReal + (b - C.toReal) - w b
        Tendsto (fun k =>
          ∑ i ∈ Finset.range (n k), e k i * κ k i)
          atTop (nhds 0) := by
  classical
  filter_upwards
    [avram_p3_f_chainlimit_original_discounted_actual_source_variation X hBV,
     avram_p3_f_chainlimit_original_raw_J_monotone X hBV]
      with ω hVar hMono
  intro J R u n ε hGrid hε hεlim hStartCap hTaylor hSourceBound e κ
  obtain ⟨M, hMnonneg, hM⟩ := hSourceBound
  let E : ℕ → ℝ := fun k =>
    ∑ i ∈ Finset.range (n k), e k i * κ k i
  have herror : ∀ k, |E k| ≤ ε k * M := by
    intro k
    have hjmono : ∀ i, i < n k →
        J ((u k) i) ≤ J ((u k) (i + 1)) := by
      intro i hi
      exact hMono ((u k) i) ((u k) (i + 1)) (hGrid k i hi)
    have hvariation := hVar (n k) (u k) q hq (hGrid k) hjmono
    have hcap :=
      avram_p3_f_chainlimit_original_discounted_cap_physical_localTaylor
        X x C hC hxc w V hVtop hVfinite D hD (u k) (n k)
        q hq hSlope (ε k) (hε k) ω (hStartCap k) (hTaylor k)
    change |E k| ≤ ε k *
      (∑ i ∈ Finset.range (n k),
        Real.exp (-(q * ((u k) i : ℝ))) *
          |X.X ((u k) (i + 1)) ω - X.X ((u k) i) ω|) at hcap
    change
      (∑ i ∈ Finset.range (n k),
        Real.exp (-(q * ((u k) i : ℝ))) *
          |X.X ((u k) (i + 1)) ω - X.X ((u k) i) ω|) ≤
        |X.drift| * (((u k) (n k) : ℝ) - ((u k) 0 : ℝ)) +
          (R ((u k) (n k)) - R ((u k) 0)) +
          (J ((u k) (n k)) - J ((u k) 0)) at hvariation
    exact (hcap.trans
      (mul_le_mul_of_nonneg_left hvariation (hε k))).trans
      (mul_le_mul_of_nonneg_left (hM k) (hε k))
  have hTop : Tendsto (fun k => ε k * M) atTop (nhds (0 : ℝ)) := by
    simpa only [zero_mul] using hεlim.mul_const M
  have hBottom : Tendsto (fun k => -(ε k * M)) atTop (nhds (0 : ℝ)) := by
    simpa only [neg_zero] using hTop.neg
  have hlow : ∀ k, -(ε k * M) ≤ E k := by
    intro k
    exact (abs_le.mp (herror k)).1
  have hhigh : ∀ k, E k ≤ ε k * M := by
    intro k
    exact (abs_le.mp (herror k)).2
  change (fun k => -(ε k * M)) ≤ E at hlow
  change E ≤ (fun k => ε k * M) at hhigh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hBottom hTop hlow hhigh
