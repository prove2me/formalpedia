-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_source14_original_dividend_rightLimit_leftLim_eq_pre
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:53:28.453408+00:00
-- url     : https://prove2.me/submissions/96568426-4604-41df-8ec3-716dec35b707

import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The left limit of the source right-payment dividend process recovers
the actual prepayment dividend at every positive time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Function.leftLim (fun s : ℝ≥0 => rightLimit D s ω) t = D t ω := by
  let f : ℝ≥0 → ℝ := fun s => D s ω
  have hmono : Monotone f := hD.2.1 ω
  have hcont : ContinuousWithinAt f (Iic t) t := hD.2.2.1 ω t
  have hsubset : Iio t ⊆ Iic t := by
    intro s hs
    exact le_of_lt (Set.mem_Iio.mp hs)
  have hleft : Tendsto f (nhdsWithin t (Iio t)) (nhds (f t)) :=
    hcont.mono hsubset
  have hLower (s : ℝ≥0) : f s ≤ rightLimit D s ω := by
    letI : Nonempty (Ioi s) :=
      ⟨⟨s + 1, by
        change s < s + 1
        exact lt_add_one s⟩⟩
    change f s ≤ (⨅ u : Ioi s, f u)
    apply le_ciInf
    intro u
    exact hmono (le_of_lt u.property)
  have hUpper (s : ℝ≥0) (hs : s < t) :
      rightLimit D s ω ≤ f t := by
    change (⨅ u : Ioi s, f u) ≤ f t
    have hBdd : BddBelow (Set.range (fun u : Ioi s => f u)) := by
      refine ⟨f s, ?_⟩
      rintro y ⟨u, rfl⟩
      exact hmono (le_of_lt u.property)
    exact ciInf_le hBdd ⟨t, hs⟩
  haveI : (nhdsWithin t (Iio t)).NeBot :=
    nhdsWithin_Iio_neBot' (show (Iio t).Nonempty from ⟨0, ht⟩) le_rfl
  have hUpperEventually :
      ∀ᶠ s in (nhdsWithin t (Iio t)), rightLimit D s ω ≤ f t := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hUpper s hs
  have hRight :
      Tendsto (fun s : ℝ≥0 => rightLimit D s ω)
        (nhdsWithin t (Iio t)) (nhds (f t)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hleft tendsto_const_nhds
      (Filter.Eventually.of_forall hLower) hUpperEventually
  exact leftLim_eq_of_tendsto hRight
