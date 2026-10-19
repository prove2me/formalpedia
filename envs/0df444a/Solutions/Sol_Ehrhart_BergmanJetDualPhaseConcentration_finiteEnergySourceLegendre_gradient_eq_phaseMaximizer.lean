-- Prove2me | solution 1 for Ehrhart.BergmanJetDualPhaseConcentration.finiteEnergySourceLegendre_gradient_eq_phaseMaximizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/3123e399-2a56-4ae4-ab7c-af245eeeece2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetDualPhaseConcentration
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open MomentRegularity MomentInteriorLegendre
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetDualPhaseConcentration
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hdu : DifferentiableAt ℝ (legendreTransform F.potential) u)
    (x : Space n)
    (hmax : ∀ z : Space n,
      phase u F.potential z ≤ phase u F.potential x) :
    SpatialBergmanFatouScheffe.actualGradient
      (legendreTransform F.potential) u = x := by
  classical
  ext i
  let v : Space n := Pi.single i (1 : ℝ)
  have hline : HasDerivAt
      (fun t : ℝ => u + t • v) v 0 := by
    simpa using
      ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have hpair : HasDerivAt
      (fun t : ℝ => pairing (u + t • v) x)
      (pairing v x) 0 := by
    simpa [SupportFunction.pairing_add_left,
      SupportFunction.pairing_smul_left] using
      ((hasDerivAt_id (0 : ℝ)).mul_const
        (pairing v x)).const_add (pairing u x)
  have hdual : HasDerivAt
      (fun t : ℝ =>
        legendreTransform F.potential (u + t • v))
      ((fderiv ℝ (legendreTransform F.potential) u) v) 0 := by
    have hu0 : u = (fun t : ℝ => u + t • v) 0 := by
      simp
    simpa [Function.comp_def] using
      hdu.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline hu0
  have hinterior :
      ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), u + t • v ∈ interior K.carrier := by
    have hmem :
        interior K.carrier ∈
          𝓝 ((fun t : ℝ => u + t • v) 0) := by
      simpa using isOpen_interior.mem_nhds hu
    exact hline.continuousAt hmem
  have hlocal : IsLocalMin
      (fun t : ℝ =>
        legendreTransform F.potential (u + t • v) -
          pairing (u + t • v) x) 0 := by
    filter_upwards [hinterior] with t ht
    have hbound :=
      finiteEnergySourcePhase_bddAbove_of_mem_interior
        F htransport ht
    have hfen :
        phase (u + t • v) F.potential x ≤
          legendreTransform F.potential (u + t • v) := by
      exact le_csSup hbound ⟨x, rfl⟩
    have hbase := legendreTransform_eq_of_maximizer x hmax
    simp only [zero_smul, add_zero]
    rw [hbase]
    unfold phase at hfen ⊢
    linarith
  have hzero :
      (fderiv ℝ (legendreTransform F.potential) u) v -
        pairing v x = 0 := by
    have hd := (hdual.sub hpair).deriv
    change
      deriv
        (fun t : ℝ =>
          legendreTransform F.potential (u + t • v) -
            pairing (u + t • v) x) 0 =
          (fderiv ℝ (legendreTransform F.potential) u) v -
            pairing v x at hd
    rw [hlocal.deriv_eq_zero] at hd
    linarith
  have hcoordinate :
      pairing
        (SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential) u) v =
        pairing x v := by
    rw [SpatialBergmanFatouScheffe.pairing_actualGradient_eq_fderiv]
    have hcomm : pairing v x = pairing x v := by
      simp [pairing, mul_comm]
    linarith
  simpa [v, pairing, Pi.single_apply] using hcoordinate
end Ehrhart.BergmanJetDualPhaseConcentration
