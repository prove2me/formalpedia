-- Prove2me | solution 1 for Ehrhart.MonomialDivergence.monomialWeight_bounded_below_on_rayTube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/2db09e77-29f2-4b73-ae7e-f3ec250ca7ca

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MonomialDivergence_supportFunction_le_pairing_add_on_rayTube

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
    (hnonempty : K.Nonempty)
    {u v : Space n}
    (hseparate : ∀ y ∈ K,
      SupportFunction.pairing y v ≤
        SupportFunction.pairing u v)
    {φ : Space n → ℝ} {C : ℝ}
    (hupper : ∀ x : Space n,
      φ x ≤ SupportFunction.supportFunction K x + C)
    {k : ℝ} (hk : 0 < k) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ rayTube v,
      c ≤ MonomialIntegrability.monomialWeight k u φ x := by
  obtain ⟨D, hD⟩ :=
    supportFunction_le_pairing_add_on_rayTube
      hcompact hnonempty hseparate
  refine ⟨Real.exp (-(k * (D + C))), Real.exp_pos _,
    fun x hx => ?_⟩
  unfold MonomialIntegrability.monomialWeight
  apply Real.exp_le_exp.mpr
  have hsupport := hD x hx
  have hpotential := hupper x
  have hlower :
      -(D + C) ≤ SupportFunction.pairing u x - φ x := by
    linarith
  calc
    -(k * (D + C)) = k * (-(D + C)) := by ring
    _ ≤ k * (SupportFunction.pairing u x - φ x) :=
      mul_le_mul_of_nonneg_left hlower hk.le
end Ehrhart.MonomialDivergence
