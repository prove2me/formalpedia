-- Prove2me | solution 1 for EnergyMomentum.classical_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T02:23:45.367191+00:00
-- url     : https://prove2.me/submissions/e1c85687-f70d-48c3-a2e6-15c822a33d83

import Definitions.Def_EnergyMomentum_basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open EnergyMomentum Filter Topology

theorem solution (m c : ℝ) (hc : 0 < c) (hm : 0 < m) :
    Filter.Tendsto
      (fun v : Vec3 => (energy m c v - m * c ^ 2 - m * ‖v‖ ^ 2 / 2) / ‖v‖ ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  let s : Vec3 → ℝ := fun v => Real.sqrt (1 - (‖v‖ / c) ^ 2)
  have hscont : Continuous s := by fun_prop
  have hs0 : s 0 = 1 := by simp [s]
  have hcont : ContinuousAt (fun v : Vec3 => m / (s v * (1 + s v)) - m / 2) 0 := by
    apply ContinuousAt.sub _ continuousAt_const
    exact continuousAt_const.div (hscont.continuousAt.mul (continuousAt_const.add hscont.continuousAt)) (by simp [hs0])
  have hlim : Tendsto (fun v : Vec3 => m / (s v * (1 + s v)) - m / 2)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    simpa [hs0, show (1 : ℝ) + 1 = 2 by norm_num] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  have hsmall : ∀ᶠ v : Vec3 in nhdsWithin 0 {0}ᶜ, ‖v‖ < c := by
    have : ∀ᶠ v : Vec3 in nhds 0, ‖v‖ < c := by
      exact (continuous_norm.tendsto 0).eventually (gt_mem_nhds (by simpa using hc))
    exact this.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ v : Vec3 in nhdsWithin 0 {0}ᶜ, v ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    simpa using hv
  filter_upwards [hsmall, hne] with v hv hv0
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  have hr0 : 0 ≤ ‖v‖ / c := div_nonneg (norm_nonneg _) hc.le
  have hr1 : ‖v‖ / c < 1 := (div_lt_one hc).mpr hv
  have hrad : 0 < 1 - (‖v‖ / c) ^ 2 := by nlinarith
  have hspos : 0 < s v := Real.sqrt_pos.2 hrad
  have hssq : (s v) ^ 2 = 1 - (‖v‖ / c) ^ 2 := Real.sq_sqrt hrad.le
  have hden : 1 + s v ≠ 0 := by positivity
  change m / (s v * (1 + s v)) - m / 2 =
    ((1 / s v * m * c ^ 2) - m * c ^ 2 - m * ‖v‖ ^ 2 / 2) / ‖v‖ ^ 2
  field_simp [hspos.ne', hden, hn, hc.ne'] at *
  nlinarith [hssq]

#print axioms solution

