-- Prove2me | solution 1 for AvramDividend.Classical.chat04_up_exit_time_pos_ae_of_positive_barrier
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:39:23.093535+00:00
-- url     : https://prove2.me/submissions/24eacc35-edb3-408b-a250-5574bb7c56e0

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_up_exit_time_pos_of_initial_safe_ceiling
import Mathlib.Topology.Order.LeftRightNhds

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 < b) :
    ∀ᵐ ω ∂P, 0 < twoSidedExitUpTime X b ω := by
  refine Filter.Eventually.of_forall fun ω => ?_
  have hc := X.rightCont ω 0
  have hU : Set.Ici (0 : ℝ≥0) = Set.univ := Set.Ici_bot
  rw [hU, continuousWithinAt_univ] at hc
  have hev : ∀ᶠ t in nhds (0 : ℝ≥0), X.X t ω ∈ Set.Iio b :=
    hc.tendsto (by rw [X.X_zero ω]; exact Iio_mem_nhds hb)
  obtain ⟨ε, hε, h⟩ := (nhds_bot_basis (α := ℝ≥0)).eventually_iff.1 hev
  exact AvramDividend.Classical.chat04_up_exit_time_pos_of_initial_safe_ceiling X b ω ε hε
    fun t ht => (h ht).le
