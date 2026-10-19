-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicConvexTransfer.convexOn_Ici_of_convexOn_Ioi_and_zero_linear_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/bcc9a4ad-a9b5-406d-82ab-ae972c6968cd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicConvexTransfer
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open MomentRegularity BergmanJetTorusEnvelope BergmanJetPartitionEndpoint
open BergmanJetJointHolomorphicStrictSchur BergmanJetJointHolomorphicPhysicalApproximation
open JetEnvelopeSlopeConvergence LogPartitionConvexity
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetJointHolomorphicConvexTransfer
theorem _root_.solution
    (f : ℝ → ℝ) (C : ℝ)
    (hfzero : f 0 = 0)
    (hfconv : ConvexOn ℝ (Set.Ioi 0) f)
    (hupper : ∀ t : ℝ, 0 < t → f t ≤ C * t) :
    ConvexOn ℝ (Set.Ici 0) f := by
  have hsegment :
      ∀ (y a b : ℝ), 0 < y → 0 ≤ a → 0 ≤ b → a + b = 1 →
        f (a * 0 + b * y) ≤ a * f 0 + b * f y := by
    intro y a b hy ha hb hab
    rcases hb.eq_or_lt with hbzero | hbpos
    · have hb0 : b = 0 := hbzero.symm
      have ha1 : a = 1 := by linarith
      simp [hb0, ha1, hfzero]
    · let e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
      have he : Tendsto e atTop (𝓝 (0 : ℝ)) := by
        exact tendsto_one_div_add_atTop_nhds_zero_nat
      have hepos (j : ℕ) : 0 < e j := by
        dsimp [e]
        positivity
      have hby : 0 < b * y := mul_pos hbpos hy
      have hcontinuity : ContinuousAt f (b * y) :=
        (hfconv.continuousOn isOpen_Ioi).continuousAt
          (isOpen_Ioi.mem_nhds hby)
      have harg :
          Tendsto
            (fun j : ℕ => a * e j + b * y)
            atTop (𝓝 (b * y)) := by
        simpa using
          (he.const_mul a).add
            (tendsto_const_nhds :
              Tendsto (fun _ : ℕ => b * y)
                atTop (𝓝 (b * y)))
      have hleft := hcontinuity.tendsto.comp harg
      have hright :
          Tendsto
            (fun j : ℕ => a * (C * e j) + b * f y)
            atTop (𝓝 (a * f 0 + b * f y)) := by
        have hCe := he.const_mul C
        have haCe := hCe.const_mul a
        have hconst :
            Tendsto (fun _ : ℕ => b * f y)
              atTop (𝓝 (b * f y)) :=
          tendsto_const_nhds
        simpa [hfzero] using haCe.add hconst
      simp only [mul_zero, zero_add]
      apply le_of_tendsto_of_tendsto hleft hright
      exact Filter.Eventually.of_forall fun j => by
        have hcv := hfconv.2 (hepos j) hy ha hb hab
        have hu := hupper (e j) (hepos j)
        change
          f (a * e j + b * y) ≤
            a * (C * e j) + b * f y
        calc
          f (a * e j + b * y) ≤
              a * f (e j) + b * f y := by
                simpa [smul_eq_mul] using hcv
          _ ≤ a * (C * e j) + b * f y := by
            gcongr
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  rcases hx.eq_or_lt with hxzero | hxpos
  · have hx0 : x = 0 := hxzero.symm
    subst x
    rcases hy.eq_or_lt with hyzero | hypos
    · have hy0 : y = 0 := hyzero.symm
      subst y
      simp [hfzero]
    · simpa [smul_eq_mul] using
        hsegment y a b hypos ha hb hab
  · rcases hy.eq_or_lt with hyzero | hypos
    · have hy0 : y = 0 := hyzero.symm
      subst y
      have hswap := hsegment x b a hxpos hb ha (by linarith)
      simpa [smul_eq_mul, add_comm] using hswap
    · simpa [smul_eq_mul] using
        hfconv.2 hxpos hypos ha hb hab
end Ehrhart.BergmanJetJointHolomorphicConvexTransfer
