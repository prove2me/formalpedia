-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.sourceTorusCoverPoint_mem_shrinkingBall_of_mem_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/ba248b09-ede1-4b5c-84f0-98a5cf3cec27

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeLocalGrowth
open Set Filter MeasureTheory Module Metric Asymptotics
open ActualJetUpperEnvelope JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace
universe u v
namespace Ehrhart.JetEnvelopeLocalGrowth
theorem _root_.solution
    {n : ℕ} {R t : ℝ}
    (hR : 0 < R)
    (q : WeightedTorusHilbert.LogTorus n)
    (hq : q ∈ sourceLocalTorusBox n (sourceLocalBoxRadius R t)) :
    dist (sourceTorusCoverPoint q)
        (0 : TorusCharacters.LogSpace n) <
      R * Real.exp (-t / 2) := by
  have he : 0 < Real.exp (-t / 2) := Real.exp_pos _
  have htarget : 0 < R * Real.exp (-t / 2) :=
    mul_pos hR he
  apply (dist_pi_lt_iff htarget).mpr
  intro i
  have hx :
      -sourceLocalBoxRadius R t < q.1 i ∧
        q.1 i < sourceLocalBoxRadius R t :=
    hq.1 i (Set.mem_univ i)
  have hangle :
      ((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) <
        sourceLocalBoxRadius R t :=
    hq.2 i (Set.mem_univ i)
  have hanglepos :
      0 < ((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) :=
    (AddCircle.equivIoc 1 0 (q.2 i)).property.1
  have habsx : |q.1 i| < sourceLocalBoxRadius R t :=
    abs_lt.mpr hx
  have hpi : 0 < 2 * Real.pi := by positivity
  have htriangle :
      ‖((q.1 i : ℂ) / 2 +
        (2 * (Real.pi : ℂ) * Complex.I) *
          (((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) : ℂ))‖ ≤
        |q.1 i| / 2 +
          (2 * Real.pi) *
            ((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) := by
    calc
      ‖((q.1 i : ℂ) / 2 +
        (2 * (Real.pi : ℂ) * Complex.I) *
          (((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) : ℂ))‖ ≤
        ‖(q.1 i : ℂ) / 2‖ +
          ‖(2 * (Real.pi : ℂ) * Complex.I) *
            (((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) : ℂ)‖ :=
        norm_add_le _ _
      _ = |q.1 i| / 2 +
          (2 * Real.pi) *
            ((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) := by
        simp [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos,
          abs_of_pos hanglepos]
  have hstrict :
      |q.1 i| / 2 +
          (2 * Real.pi) *
            ((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) <
        sourceLocalBoxRadius R t / 2 +
          (2 * Real.pi) * sourceLocalBoxRadius R t :=
    add_lt_add
      (div_lt_div_of_pos_right habsx (by norm_num))
      (mul_lt_mul_of_pos_left hangle hpi)
  have hden : 0 < 1 + 4 * Real.pi := by positivity
  have hscale :
      sourceLocalBoxScale R * (1 + 4 * Real.pi) ≤ R := by
    apply (le_div_iff₀ hden).mp
    exact min_le_right _ _
  have hradius :
      sourceLocalBoxRadius R t / 2 +
          (2 * Real.pi) * sourceLocalBoxRadius R t <
        R * Real.exp (-t / 2) := by
    unfold sourceLocalBoxRadius
    calc
      sourceLocalBoxScale R * Real.exp (-t / 2) / 2 +
          (2 * Real.pi) *
            (sourceLocalBoxScale R * Real.exp (-t / 2)) =
        ((sourceLocalBoxScale R * (1 + 4 * Real.pi)) / 2) *
          Real.exp (-t / 2) := by ring
      _ ≤ (R / 2) * Real.exp (-t / 2) := by
        gcongr
      _ < R * Real.exp (-t / 2) := by
        nlinarith [mul_pos hR he]
  simpa [sourceTorusCoverPoint,
    JointHolomorphicLaurentFourierCompatibility.logarithmicPoint,
    dist_zero_right] using
      lt_of_le_of_lt htriangle (hstrict.trans hradius)
end Ehrhart.JetEnvelopeLocalGrowth
