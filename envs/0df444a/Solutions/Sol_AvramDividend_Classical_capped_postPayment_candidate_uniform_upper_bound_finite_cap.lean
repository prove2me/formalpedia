-- Prove2me | solution 1 for AvramDividend.Classical.capped_postPayment_candidate_uniform_upper_bound_finite_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:39:30.463244+00:00
-- url     : https://prove2.me/submissions/1fce8240-806a-4af4-8f63-6e6920e342b6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ω : Ω) (t : ℝ≥0),
      w (x + X.X t ω - rightLimit D t ω) ≤ B := by
  have hcont : ContinuousOn w (Icc (0 : ℝ) c) := by
    apply hw_cont.mono
    intro y hy
    exact hy.1
  have hbound : BddAbove (w '' Icc (0 : ℝ) c) :=
    isCompact_Icc.bddAbove_image hcont
  obtain ⟨M, hM⟩ := hbound
  refine ⟨max 0 M, le_max_left 0 M, ?_⟩
  intro ω t
  let y : ℝ := x + X.X t ω - rightLimit D t ω
  change w y ≤ max 0 M
  by_cases hy : y < 0
  · rw [hw_neg y hy]
    exact le_max_left 0 M
  · have hy0 : 0 ≤ y := le_of_not_gt hy
    have hcap : ENNReal.ofReal y ≤ ENNReal.ofReal c :=
      capped_postPaymentReserve_ofReal_le_cap
        X x (ENNReal.ofReal c) D hD hxc ω t
    have hyc : y ≤ c :=
      (ENNReal.ofReal_le_ofReal_iff hc).mp hcap
    have hmem : y ∈ Icc (0 : ℝ) c := ⟨hy0, hyc⟩
    have hval : w y ≤ M :=
      hM (Set.mem_image_of_mem w hmem)
    exact hval.trans (le_max_right 0 M)
