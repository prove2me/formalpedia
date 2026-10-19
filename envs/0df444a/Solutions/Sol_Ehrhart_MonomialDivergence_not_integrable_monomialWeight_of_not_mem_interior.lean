-- Prove2me | solution 1 for Ehrhart.MonomialDivergence.not_integrable_monomialWeight_of_not_mem_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/5bbb41ef-fc4b-44bb-b586-48e2b68f732f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MonomialDivergence_exists_separating_direction
import Theorems.Thm_Ehrhart_MonomialDivergence_rayTube_volume_eq_top
import Theorems.Thm_Ehrhart_MonomialDivergence_monomialWeight_bounded_below_on_rayTube

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MonomialDivergence
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace Ehrhart.MonomialDivergence
theorem _root_.solution {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    (hconvex : Convex ℝ K)
    (hinterior : (interior K).Nonempty)
    {u : Space n} (hu : u ∉ interior K)
    {φ : Space n → ℝ} {C : ℝ}
    (hupper : ∀ x : Space n,
      φ x ≤ SupportFunction.supportFunction K x + C)
    {k : ℝ} (hk : 0 < k) :
    ¬ Integrable (MonomialIntegrability.monomialWeight k u φ)
      (volume : Measure (Space n)) := by
  obtain ⟨v, hv, hseparate⟩ :=
    exists_separating_direction hconvex hinterior hu
  have hnonempty : K.Nonempty := hinterior.mono interior_subset
  obtain ⟨c, hc, hweight⟩ :=
    monomialWeight_bounded_below_on_rayTube
      hcompact hnonempty hseparate hupper hk
  intro hintegrable
  have hscaled :
      Integrable
        (fun x : Space n =>
          c⁻¹ * MonomialIntegrability.monomialWeight k u φ x)
        (volume : Measure (Space n)) :=
    hintegrable.const_mul c⁻¹
  have hnonnegative :
      0 ≤ᵐ[(volume : Measure (Space n))]
        (fun x : Space n =>
          c⁻¹ * MonomialIntegrability.monomialWeight k u φ x) := by
    filter_upwards [] with x
    exact mul_nonneg (inv_nonneg.mpr hc.le)
      (Real.exp_pos _).le
  have hlarge :
      ∀ x ∈ rayTube v,
        (1 : ℝ) ≤
          c⁻¹ * MonomialIntegrability.monomialWeight k u φ x := by
    intro x hx
    calc
      (1 : ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ c⁻¹ *
        MonomialIntegrability.monomialWeight k u φ x :=
        mul_le_mul_of_nonneg_left (hweight x hx)
          (inv_nonneg.mpr hc.le)
  have hmeasure := hscaled.measure_le_integral hnonnegative hlarge
  rw [rayTube_volume_eq_top v hv] at hmeasure
  exact ENNReal.ofReal_ne_top (top_unique hmeasure)
end Ehrhart.MonomialDivergence
