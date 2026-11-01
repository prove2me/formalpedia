-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_original_controlled_jump_support_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:10:35.457466+00:00
-- url     : https://prove2.me/submissions/ba70120f-5c6e-425d-936a-fab4795c704d

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

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
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    (x + X.X t ω - rightLimit D t ω ≠
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ↔
      (X.X t ω ≠ Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ∨
        rightLimit D t ω ≠ D t ω) := by
  rw [avram_wave3_04_postPaymentReserve_exact_leftLim_identity
    X x D hD ω t ht]
  have hX : X.X t ω -
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≤ 0 :=
    avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω t ht
  have hDle : D t ω ≤ rightLimit D t ω :=
    dividendStrategy_le_rightLimit D hD ω t
  constructor
  · intro hneq
    by_contra hno
    push_neg at hno
    obtain ⟨hxeq, hdeq⟩ := hno
    apply hneq
    rw [hxeq, hdeq]
  · intro hj
    intro heq
    have hxeq : X.X t ω =
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t := by
      linarith
    have hdeq : rightLimit D t ω = D t ω := by
      linarith
    exact hj.elim (fun hx => hx hxeq) (fun hd => hd hdeq)