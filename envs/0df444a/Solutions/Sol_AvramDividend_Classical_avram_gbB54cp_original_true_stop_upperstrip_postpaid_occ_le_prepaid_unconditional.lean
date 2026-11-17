-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54cp_original_true_stop_upperstrip_postpaid_occ_le_prepaid_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:32:15.139195+00:00
-- url     : https://prove2.me/submissions/18e08d10-3506-4097-a9a1-b7b14797b2d4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_true_stopped_upperstrip_prepost_occupation_integral_eq_ae
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (ω : Ω) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
        b < x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) ≤
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
        b < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) := by 
  exact (avram_gbB54cp_true_stopped_upperstrip_prepost_occupation_integral_eq_ae X x b D hD n ρ ω).symm.le
