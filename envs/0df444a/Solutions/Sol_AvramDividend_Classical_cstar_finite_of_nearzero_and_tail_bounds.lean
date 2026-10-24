-- Prove2me | solution 1 for AvramDividend.Classical.cstar_finite_of_nearzero_and_tail_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:56:50.702777+00:00
-- url     : https://prove2.me/submissions/b3154851-bcb0-484f-84f7-6713afea0be2

import Mathlib.Topology.Order.Compact
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_minimizer

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set
open scoped ENNReal

/-- A compact derivative-minimising band with controlled tails has a
    positive global minimiser, so the canonical barrier is finite. -/
theorem solution
    (W : ℝ → ℝ) (a δ M : ℝ)
    (ha : 0 < a) (hδ : 0 < δ) (hδa : δ < a) (haM : a < M)
    (hcont : ContinuousOn (deriv W) (Set.Ioi 0))
    (hnear : ∀ x : ℝ, 0 < x → x < δ → deriv W a ≤ deriv W x)
    (htail : ∀ x : ℝ, M < x → deriv W a ≤ deriv W x) :
    cstar W < ⊤ := by
  have hacomp : a ∈ Set.Icc δ M := ⟨hδa.le, haM.le⟩
  have hreg : ContinuousOn (deriv W) (Set.Icc δ M) :=
    hcont.mono (by
      intro x hx
      exact lt_of_lt_of_le hδ hx.1)
  obtain ⟨b, hb, hbmin⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc δ M)).exists_isMinOn
      ⟨a, hacomp⟩ hreg
  have hbpos : 0 < b := lt_of_lt_of_le hδ hb.1
  have hba : deriv W b ≤ deriv W a := hbmin hacomp
  have hglobal : ∀ x : ℝ, 0 < x → deriv W b ≤ deriv W x := by
    intro x hx
    by_cases hxδ : x < δ
    · exact hba.trans (hnear x hx hxδ)
    · by_cases hxM : M < x
      · exact hba.trans (htail x hxM)
      · exact hbmin ⟨le_of_not_gt hxδ, le_of_not_gt hxM⟩
  exact cstar_lt_top_of_minimizer W ⟨b, hbpos, hglobal⟩
