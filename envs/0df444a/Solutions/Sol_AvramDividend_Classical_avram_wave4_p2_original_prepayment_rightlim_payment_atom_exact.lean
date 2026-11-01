-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_original_prepayment_rightlim_payment_atom_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:37:11.739826+00:00
-- url     : https://prove2.me/submissions/11d130a6-88c3-408c-b8b2-ac74d67bffa7

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_tendsto_postPaymentReserve_right

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    Function.rightLim (fun s : ℝ≥0 => riskProcess X x D s ω) t =
      x + X.X t ω - rightLimit D t ω ∧
    (Function.rightLim (fun s : ℝ≥0 => riskProcess X x D s ω) t ≠
      riskProcess X x D t ω ↔
      rightLimit D t ω ≠ D t ω) := by
  letI : (𝓝[>] t).NeBot :=
    nhdsGT_neBot_of_exists_gt ⟨t + 1, lt_add_one t⟩
  have hr :
      Function.rightLim (fun s : ℝ≥0 => riskProcess X x D s ω) t =
        x + X.X t ω - rightLimit D t ω :=
    rightLim_eq_of_tendsto
      (riskProcess_tendsto_postPaymentReserve_right X x D hD ω t)
  refine ⟨hr, ?_⟩
  rw [hr]
  change (x + X.X t ω - rightLimit D t ω ≠
      x + X.X t ω - D t ω) ↔
    rightLimit D t ω ≠ D t ω
  constructor
  · intro h heq
    apply h
    rw [heq]
  · intro h heq
    apply h
    linarith