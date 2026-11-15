-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb30_original_any_constant_reserve_weighted_stieltjes_cash_equals_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:02:24.689312+00:00
-- url     : https://prove2.me/submissions/efe97a6c-8779-4083-8ab0-464370459f02

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb29_original_constant_pre_right_reserve_stieltjes_exact_drift
import Theorems.Thm_AvramDividend_Classical_measure_restrict_Ioc_eq_of_local_Ioc_agreement
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0) (k : ℝ) (hDrift : 0 ≤ X.drift)
    (hReserve : ∀ t : ℝ≥0, t ≤ T → riskProcess X x D t ω = k)
    (hNoAtom : ∀ t : ℝ≥0, t ≤ T → rightLimit D t ω = D t ω)
    (hSourceLine : ∀ a b : ℝ≥0, a ≤ b → b ≤ T →
      X.X b ω - X.X a ω = X.drift * ((b : ℝ) - (a : ℝ))) :
    ∀ f : ℝ → ℝ≥0∞,
      (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
        ∂(dividendMeasure D ω)) =
      (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
        ∂((ENNReal.ofReal X.drift) • volume))  := by
  intro f
  let μ : Measure ℝ := dividendMeasure D ω
  let ν : Measure ℝ := (ENNReal.ofReal X.drift) • volume
  have hCash (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
      (ht : t ≤ (T : ℝ)) :
      (dividendMeasure D ω) (Ioc s t) =
        ENNReal.ofReal (X.drift * (t - s)) := by
    let ss : ℝ≥0 := ⟨s, hs⟩
    let tt : ℝ≥0 := ⟨t, le_trans hs hst⟩
    have hstNN : ss ≤ tt := hst
    have htNN : tt ≤ T := ht
    have hssT : ss ≤ T := hstNN.trans htNN
    have hcell :=
      avram_bvb29_original_constant_pre_right_reserve_stieltjes_exact_drift
        X x C D hD ω ss tt hstNN k
        (hReserve ss hssT) (hReserve tt htNN)
        (hNoAtom ss hssT) (hNoAtom tt htNN)
        (hSourceLine ss tt hstNN htNN)
    change (dividendMeasure D ω) (Ioc s t) =
      ENNReal.ofReal (X.drift * (t - s)) at hcell
    exact hcell
  have hFiniteCash : μ (Ioc (0 : ℝ) (T : ℝ)) < ⊤ := by
    change (dividendMeasure D ω) (Ioc (0 : ℝ) (T : ℝ)) < ⊤
    rw [hCash 0 (T : ℝ) (le_refl _)
      (by exact_mod_cast (show (0 : ℝ≥0) ≤ T from zero_le)) le_rfl]
    exact ENNReal.ofReal_lt_top
  have hMass (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
      (ht : t ≤ (T : ℝ)) : μ (Ioc s t) = ν (Ioc s t) := by
    change (dividendMeasure D ω) (Ioc s t) =
      ((ENNReal.ofReal X.drift) • volume) (Ioc s t)
    rw [hCash s t hs hst ht]
    simpa [Measure.smul_apply, Real.volume_Ioc, smul_eq_mul] using
      (ENNReal.ofReal_mul hDrift :
        ENNReal.ofReal (X.drift * (t - s)) =
          ENNReal.ofReal X.drift * ENNReal.ofReal (t - s))
  have heq : μ.restrict (Ioc (0 : ℝ) (T : ℝ)) =
      ν.restrict (Ioc (0 : ℝ) (T : ℝ)) :=
    measure_restrict_Ioc_eq_of_local_Ioc_agreement
      μ ν (T : ℝ)
      (by exact_mod_cast (show (0 : ℝ≥0) ≤ T from zero_le))
      hFiniteCash hMass
  exact congrArg (fun m : Measure ℝ => ∫⁻ t, f t ∂m) heq
