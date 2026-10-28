-- Prove2me | solution 1 for BilevelSOC.SecondOrder.hadamard_of_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:01:21.85228+00:00
-- url     : https://prove2.me/submissions/19f04272-e735-4bb8-81c9-1755a60355ab

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Model
open scoped Topology

open BilevelSOC.SecondOrder in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (θ : V → ℝ) (x : V) (θ' : V → ℝ)
    (U : Set V) (hU : U ∈ 𝓝 x) (L : NNReal)
    (hLip : LipschitzOnWith L θ U)
    (hDiff : ∀ d, HasDirDerivAt θ x d (θ' d)) :
    ∀ d, HasHadamardDirDerivAt θ x d (θ' d) := by
  intro d
  unfold HasHadamardDirDerivAt
  have hF : (𝓝[>] (0:ℝ)) ×ˢ 𝓝 d ≤ 𝓝 ((0:ℝ), d) := by
    rw [nhds_prod_eq]; exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
  have h1 : Filter.Tendsto (fun r : ℝ × V => x + r.1 • r.2) ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 d) (𝓝 x) := by
    have : Filter.Tendsto (fun r : ℝ × V => x + r.1 • r.2) (𝓝 ((0:ℝ), d))
        (𝓝 (x + (0:ℝ) • d)) :=
      ((continuous_const.add (continuous_fst.smul continuous_snd)).tendsto _)
    simpa using this.mono_left hF
  have h2 : Filter.Tendsto (fun r : ℝ × V => x + r.1 • d) ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 d) (𝓝 x) := by
    have : Filter.Tendsto (fun r : ℝ × V => x + r.1 • d) (𝓝 ((0:ℝ), d))
        (𝓝 (x + (0:ℝ) • d)) :=
      ((continuous_const.add (continuous_fst.smul continuous_const)).tendsto _)
    simpa using this.mono_left hF
  have hpos : ∀ᶠ r : ℝ × V in (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 d, r.1 ∈ Set.Ioi (0:ℝ) :=
    Filter.tendsto_fst.eventually eventually_mem_nhdsWithin
  have hB : Filter.Tendsto (fun r : ℝ × V => (θ (x + r.1 • d) - θ x) / r.1)
      ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 d) (𝓝 (θ' d)) := (hDiff d).comp Filter.tendsto_fst
  have hN : Filter.Tendsto (fun r : ℝ × V => (L:ℝ) * ‖r.2 - d‖)
      ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 d) (𝓝 0) := by
    have h3 : Filter.Tendsto (fun r : ℝ × V => ‖r.2 - d‖) ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 d) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp Filter.tendsto_snd
    simpa using h3.const_mul (L:ℝ)
  have hA : Filter.Tendsto (fun r : ℝ × V => (θ (x + r.1 • r.2) - θ (x + r.1 • d)) / r.1)
      ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 d) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hN
    filter_upwards [h1 hU, h2 hU, hpos] with r hr1 hr2 hr0
    have hr0' : 0 < r.1 := hr0
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr0', div_le_iff₀ hr0']
    have hl := hLip.dist_le_mul _ hr1 _ hr2
    rw [Real.dist_eq, dist_eq_norm] at hl
    calc |θ (x + r.1 • r.2) - θ (x + r.1 • d)| ≤ L * ‖(x + r.1 • r.2) - (x + r.1 • d)‖ := hl
      _ = L * ‖r.2 - d‖ * r.1 := by
        rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr0']
        ring
  have := hA.add hB
  rw [zero_add] at this
  exact this.congr (fun r => by ring)
