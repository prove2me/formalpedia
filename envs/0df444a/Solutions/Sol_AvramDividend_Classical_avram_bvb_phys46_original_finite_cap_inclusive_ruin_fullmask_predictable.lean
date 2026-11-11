-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys46_original_finite_cap_inclusive_ruin_fullmask_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:26:23.346553+00:00
-- url     : https://prove2.me/submissions/9e2fb3ee-d447-4e0c-96f2-2426f2e78c00

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_stopped_compact_previsible

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The exact finite-cap original pre-ruin full mask is predictable, including zero and cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    MeasurableSet[𝓕.rightCont.predictable]
      {p | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        0 ≤ U p ∧ ENNReal.ofReal (U p) ≤ C} := by
  intro τ U
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hBand :=
    (avram_p3_g_localise_original_ruin_stopped_compact_previsible
      X x D hStrategy T 0 C.toReal).2.2.1
  simpa only [Set.mem_Icc, ENNReal.ofReal_le_iff_le_toReal hFinite,
    and_assoc] using hBand
