-- Prove2me | solution 1 for AvramDividend.Classical.derivZeroPlus_eq_min_of_accumulated_minimizers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T22:59:56.967767+00:00
-- url     : https://prove2.me/submissions/ca453873-b944-4974-8cf0-fc5c529c9a58

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_deriv_global_lower_le_right_liminf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter Set Topology
open scoped Topology ENNReal

/-- Positive derivative minimisers that accumulate at zero force the
one-sided derivative liminf to equal their common real minimum. -/
theorem solution (W : ℝ → ℝ)
    (hS : (cstarSet W).Nonempty)
    (hzero : sInf (cstarSet W) = 0)
    (a : ℝ) (ha : a ∈ cstarSet W) :
    derivZeroPlus W = ((deriv W a : ℝ) : EReal) := by
  have hb : BddBelow (cstarSet W) := by
    refine ⟨0, ?_⟩
    intro x hx
    exact hx.1.le
  have hcl : (0 : ℝ) ∈ closure (cstarSet W) := by
    simpa [hzero] using (csInf_mem_closure hS hb)
  have hfreqS : ∃ᶠ x in 𝓝 (0 : ℝ), x ∈ cstarSet W :=
    (mem_closure_iff_frequently).mp hcl
  have hfreq :
      ∃ᶠ x in 𝓝[>] (0 : ℝ),
        ((deriv W x : ℝ) : EReal) ≤ ((deriv W a : ℝ) : EReal) := by
    apply (frequently_nhdsWithin_iff).2
    exact hfreqS.mono (by
      intro x hx
      refine ⟨?_, hx.1⟩
      exact_mod_cast hx.2 a ha.1)
  have hupper : derivZeroPlus W ≤ ((deriv W a : ℝ) : EReal) := by
    unfold derivZeroPlus
    exact Filter.liminf_le_of_frequently_le hfreq
  have hlower : ((deriv W a : ℝ) : EReal) ≤ derivZeroPlus W :=
    deriv_global_lower_le_right_liminf W (deriv W a) ha.2
  exact le_antisymm hupper hlower
