-- Prove2me | solution 1 for BHTOpinion.Continuum.theorem5_convergence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T23:43:50.860072+00:00
-- url     : https://prove2.me/submissions/061c7931-0500-4bab-aa47-c5151b2e95d7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model
import Theorems.Thm_BHTOpinion_Continuum_theorem4_existence_uniqueness
import Theorems.Thm_BHTOpinion_Continuum_prop2_pointwise_convergence
import Theorems.Thm_BHTOpinion_Continuum_prop3a_limit_in_Fbar
import Theorems.Thm_BHTOpinion_Continuum_prop3b_F_fixed_point
import Theorems.Thm_BHTOpinion_Continuum_prop3c_fixed_point_in_Fbar

open MeasureTheory Filter Topology

open BHTOpinion.Continuum in
theorem solution (x0 : ℝ → ℝ) (x : ℝ → ℝ → ℝ) (hx : IsSolution x0 x)
    (hreg : Regular (x 0) ∨ ∀ t : ℝ, 0 ≤ t → InX (x t)) :
    (∃ y : ℝ → ℝ, InFbar y ∧
      ∀ᵐ α ∂(volume.restrict I), Tendsto (fun t => x t α) atTop (𝓝 (y α))) ∧
    {s : ℝ → ℝ | InF s} ⊆ {s | InX s ∧ IsFixedPoint s} ∧
    {s : ℝ → ℝ | InX s ∧ IsFixedPoint s} ⊆ {s | InFbar s} := by
  classical
  -- monotonicity of the trajectory
  have hmono : ∀ t : ℝ, 0 ≤ t → InX (x t) := by
    rcases hreg with ⟨m, M, hm, hM, hXm, hXM⟩ | h
    · obtain ⟨z, _hz, _, huniq, _, _, hzreg⟩ :=
        theorem4_existence_uniqueness m M hm hM (x 0) hXm hXM
      have hx' : IsSolution (x 0) x := by
        refine ⟨hx.measurable, hx.mem_Y, hx.integrable, fun t ht α hα => ?_⟩
        have h0 := hx.eq 0 le_rfl α hα
        simp only [intervalIntegral.integral_same, add_zero] at h0
        rw [hx.eq t ht α hα, h0]
      intro t ht
      have heq := huniq x hx' t ht
      obtain ⟨m', M', _, _, hz1, _⟩ := hzreg t ht
      obtain ⟨hzmono, C, hC⟩ := hz1.1
      refine ⟨fun a ha b hb hab => ?_, C, fun a ha => ?_⟩
      · rw [heq a ha, heq b hb]; exact hzmono ha hb hab
      · rw [heq a ha]; exact hC a ha
    · exact h
  refine ⟨?_, fun s hs => ⟨hs.1, prop3b_F_fixed_point s hs⟩,
    fun s hs => prop3c_fixed_point_in_Fbar s hs.1 hs.2⟩
  obtain ⟨S, hS, hconv⟩ := prop2_pointwise_convergence x0 x hx hmono
  let y : ℝ → ℝ := fun α =>
    if h : ∃ l, Tendsto (fun t => x t α) atTop (𝓝 l) then h.choose else 0
  have hyconv : ∀ᵐ α ∂(volume.restrict I), Tendsto (fun t => x t α) atTop (𝓝 (y α)) := by
    have hSnull : volume S = 0 := hS.measure_zero volume
    have h1 : ∀ᵐ α ∂(volume.restrict I), α ∉ S :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hSnull)
    have h2 : ∀ᵐ α ∂(volume.restrict I), α ∈ I := ae_restrict_mem measurableSet_Icc
    filter_upwards [h1, h2] with α hαS hαI
    have hex := hconv α hαI hαS
    simp only [y, dif_pos hex]
    exact hex.choose_spec
  obtain ⟨y', hy'F, hy'eq⟩ := prop3a_limit_in_Fbar x0 x hx hmono y hyconv
  refine ⟨y', hy'F, ?_⟩
  filter_upwards [hyconv, hy'eq] with α h1 h2
  rw [h2]; exact h1
