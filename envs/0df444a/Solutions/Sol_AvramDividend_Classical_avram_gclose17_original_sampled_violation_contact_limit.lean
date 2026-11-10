-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose17_original_sampled_violation_contact_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T01:02:17.585196+00:00
-- url     : https://prove2.me/submissions/1b861616-cacd-4fa3-819c-fee6ff1ff978

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_postrightpayment_reserve_pathwise_rightcontinuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Right-continuity carries strict sampled violations to weak contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (δ : ℝ) (u : ℕ → ℝ≥0)
    (hu : Tendsto u atTop (𝓝[Ici t] t))
    (hbelow : ∀ n, x + X.X (u n) ω - rightLimit D (u n) ω < δ) :
    x + X.X t ω - rightLimit D t ω ≤ δ := by
  have hcont := avram_p4_e_localise_original_postrightpayment_reserve_pathwise_rightcontinuous
    X x D hD ω t
  have hlim : Tendsto
      (fun n => x + X.X (u n) ω - rightLimit D (u n) ω) atTop
      (𝓝 (x + X.X t ω - rightLimit D t ω)) :=
    hcont.tendsto.comp hu
  have hclosed : x + X.X t ω - rightLimit D t ω ∈ Iic δ :=
    isClosed_Iic.mem_of_tendsto hlim
      (Filter.Eventually.of_forall (fun n => le_of_lt (hbelow n)))
  exact hclosed
