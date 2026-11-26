-- Prove2me | solution 1 for Eden.tendsto_div_time_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:25:33.028141+00:00
-- url     : https://prove2.me/submissions/82728aba-b144-43d5-8ce7-927d056fd23e

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_Eden_RealTimeAverages

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {f f' : ℝ → ℝ} {L : ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t)
    (hlim : Tendsto f' atTop (𝓝 L)) :
    Tendsto (fun t => f t / t) atTop (𝓝 L) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (by positivity)
  let T := max 0 N
  let e := fun t => f t - L * t
  have hT₀ : 0 ≤ T := le_max_left _ _
  have hNT : N ≤ T := le_max_right _ _
  have hderiv : ∀ t ∈ Ici T, HasDerivWithinAt e (f' t - L) (Ici T) t := by
    intro t ht
    convert! ((hf t (hT₀.trans ht)).sub
      ((hasDerivAt_id t).const_mul L)).hasDerivWithinAt (s := Ici T) using 1
    simp
  have hbound : ∀ t ∈ Ici T, ‖f' t - L‖ ≤ ε / 2 := by
    intro t ht
    exact le_of_lt (by simpa [Real.dist_eq, Real.norm_eq_abs] using hN t (hNT.trans ht))
  have hc : Tendsto (fun t : ℝ => e T / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hc (ε / 2) (by positivity)
  refine ⟨max 1 (max T M), ?_⟩
  intro t ht
  have ht₁ : 1 ≤ t := (le_max_left _ _).trans ht
  have htT : T ≤ t := (le_max_left T M).trans ((le_max_right _ _).trans ht)
  have htM : M ≤ t := (le_max_right T M).trans ((le_max_right _ _).trans ht)
  have ht₀ : 0 < t := by linarith
  have htail := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (convex_Ici T) (show T ∈ Ici T from Set.mem_Ici.mpr (le_refl T))
      (show t ∈ Ici T from htT)
  have htail' : |e t - e T| ≤ ε / 2 * (t - T) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr htT)] using htail
  have he : |e t| ≤ ε / 2 * t + |e T| := by
    have htri : |e t| ≤ |e t - e T| + |e T| := by
      simpa only [sub_add_cancel] using abs_add_le (e t - e T) (e T)
    have hpos := mul_nonneg (show 0 ≤ ε / 2 by positivity) hT₀
    linarith
  have hsmall : |e T| / t < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero, abs_div, abs_of_pos ht₀] using hM t htM
  rw [Real.dist_eq]
  calc
    |f t / t - L| = |e t| / t := by
      have heq : f t / t - L = e t / t := by
        dsimp [e]
        field_simp
      rw [heq, abs_div, abs_of_pos ht₀]
    _ ≤ ε / 2 + |e T| / t := by
      apply (div_le_iff₀ ht₀).mpr
      calc
        |e t| ≤ ε / 2 * t + |e T| := he
        _ = (ε / 2 + |e T| / t) * t := by field_simp
    _ < ε := by linarith
end Eden
