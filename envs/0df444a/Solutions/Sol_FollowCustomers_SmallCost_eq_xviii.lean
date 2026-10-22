-- Prove2me | solution 1 for FollowCustomers.SmallCost.eq_xviii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:08:35.135835+00:00
-- url     : https://prove2.me/submissions/900fcf57-76b1-4321-a652-400774f1d02e

import Mathlib
set_option autoImplicit false
open Filter Topology

theorem solution :
    Tendsto (fun G : ℝ => (Real.log G - 2 * (G - 1) / (G + 1)) / (G - 1) ^ 3)
      (𝓝[≠] 1) (𝓝 (1 / 12)) := by
  have hpos : ∀ᶠ x : ℝ in 𝓝 1, 0 < x := Ioi_mem_nhds one_pos
  have hf : ∀ᶠ x : ℝ in 𝓝 1, HasDerivAt (fun G : ℝ => Real.log G - 2 * (G - 1) / (G + 1))
      (1 / x - 4 / (x + 1) ^ 2) x := by
    filter_upwards [hpos] with x hx
    have hne : x + 1 ≠ 0 := by linarith
    have h1 := Real.hasDerivAt_log hx.ne'
    have h2 : HasDerivAt (fun G : ℝ => 2 * (G - 1)) 2 x := by
      simpa using ((hasDerivAt_id x).sub_const 1).const_mul 2
    have h3 : HasDerivAt (fun G : ℝ => G + 1) 1 x := (hasDerivAt_id x).add_const 1
    have h4 := h1.sub (h2.div h3 hne)
    have h5 : HasDerivAt (fun G : ℝ => Real.log G - 2 * (G - 1) / (G + 1))
        (x⁻¹ - (2 * (x + 1) - 2 * (x - 1) * 1) / (x + 1) ^ 2) x := h4
    refine h5.congr_deriv ?_
    field_simp
    ring
  have hg : ∀ᶠ x : ℝ in 𝓝 1, HasDerivAt (fun G : ℝ => (G - 1) ^ 3) (3 * (x - 1) ^ 2) x := by
    refine Eventually.of_forall (fun x => ?_)
    have h5 : HasDerivAt (fun G : ℝ => (G - 1) ^ 3) (((3 : ℕ) : ℝ) * (x - 1) ^ (3 - 1) * 1) x :=
      ((hasDerivAt_id x).sub_const 1).pow 3
    refine h5.congr_deriv ?_
    norm_num
  have hg' : ∀ᶠ x : ℝ in 𝓝[≠] 1, 3 * (x - 1) ^ 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    positivity
  have hfa : Tendsto (fun G : ℝ => Real.log G - 2 * (G - 1) / (G + 1)) (𝓝 1) (𝓝 0) := by
    have hc : ContinuousAt (fun G : ℝ => Real.log G - 2 * (G - 1) / (G + 1)) 1 := by
      apply ContinuousAt.sub
      · exact Real.continuousAt_log one_ne_zero
      · apply ContinuousAt.div (by fun_prop) (by fun_prop)
        norm_num
    have := hc.tendsto
    simpa using this
  have hga : Tendsto (fun G : ℝ => (G - 1) ^ 3) (𝓝 1) (𝓝 0) := by
    have hc : Continuous (fun G : ℝ => (G - 1) ^ 3) := by fun_prop
    simpa using hc.tendsto 1
  have hdiv : Tendsto (fun x : ℝ => (1 / x - 4 / (x + 1) ^ 2) / (3 * (x - 1) ^ 2))
      (𝓝[≠] 1) (𝓝 (1 / 12)) := by
    have hc : ContinuousAt (fun x : ℝ => 1 / (3 * x * (x + 1) ^ 2)) 1 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      norm_num
    have ht : Tendsto (fun x : ℝ => 1 / (3 * x * (x + 1) ^ 2)) (𝓝[≠] 1) (𝓝 (1 / 12)) := by
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
      convert this using 2
      norm_num
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin, (Ioi_mem_nhds one_pos : Set.Ioi (0 : ℝ) ∈ 𝓝 (1 : ℝ)) |> fun h => nhdsWithin_le_nhds h] with x hx hx0
    have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    have hx0' : 0 < x := hx0
    have hx2 : x + 1 ≠ 0 := by linarith
    field_simp
    ring
  exact HasDerivAt.lhopital_zero_nhdsNE (eventually_nhdsWithin_of_eventually_nhds hf)
    (eventually_nhdsWithin_of_eventually_nhds hg) hg' (hfa.mono_left nhdsWithin_le_nhds)
    (hga.mono_left nhdsWithin_le_nhds) hdiv
