-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.tangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:21:12.672666+00:00
-- url     : https://prove2.me/submissions/c211750d-75e0-437e-9d54-d4b773406d58

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_dom_open
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_chart_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_chart_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_mulB_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cT_apply
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {Y : J k r → ℝ} (hY : Y ∈ Dom k r) (W : J k r → ℝ) :
    inLie k r (-(fderiv ℝ (chart g0) Y W) * (chart g0 Y)⁻¹) := by
  set c := chart g0 Y with hc
  set T := fderiv ℝ (chart g0) Y W with hT
  have hcG : c ∈ GV k r := chart_mem hg0 hY
  have hcu : IsUnit c.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hcG
  set γ : ℝ → Mat k r := fun t => chart g0 (Y + t • W) with hγ
  have hline : HasDerivAt (fun t : ℝ => Y + t • W) W 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).smul_const W).const_add Y
    rw [one_smul] at h
    exact h
  have hγd : HasDerivAt γ T 0 :=
    (chart_diff g0 hY).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hγ0 : γ 0 = c := by simp [hγ, hc]
  have h1 : HasDerivAt (fun t => cT k r (γ t)) (cT k r T) 0 :=
    (cT k r).hasFDerivAt.comp_hasDerivAt 0 hγd
  have h2 : HasDerivAt (fun t => mulB k r (cT k r (γ t)) (Hpk k r))
      (mulB k r (cT k r (γ 0)) 0 + mulB k r (cT k r T) (Hpk k r)) 0 :=
    ContinuousLinearMap.hasDerivAt_of_bilinear (fun _ => h1) (fun _ => hasDerivAt_const _ _)
  have h3 : HasDerivAt (fun t => mulB k r (mulB k r (cT k r (γ t)) (Hpk k r)) (γ t))
      (mulB k r (mulB k r (cT k r (γ 0)) (Hpk k r)) T +
        mulB k r (mulB k r (cT k r (γ 0)) 0 + mulB k r (cT k r T) (Hpk k r)) (γ 0)) 0 :=
    ContinuousLinearMap.hasDerivAt_of_bilinear (fun _ => h2) (fun _ => hγd)
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), Y + t • W ∈ Dom k r :=
    ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt (x := (0:ℝ))).preimage_mem_nhds
      (dom_open.mem_nhds (by simpa using hY))
  have h4 : HasDerivAt (fun t => mulB k r (mulB k r (cT k r (γ t)) (Hpk k r)) (γ t)) 0 0 := by
    refine (hasDerivAt_const (0:ℝ) (Hpk k r)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    have hm : γ t ∈ GV k r := chart_mem hg0 ht
    exact hm
  have hz := h3.unique h4
  simp only [mulB_apply, cT_apply, hγ0, Matrix.mul_zero, zero_add] at hz

  have hci : c * c⁻¹ = 1 := Matrix.mul_nonsing_inv _ hcu
  have hci' : (c⁻¹)ᴴ * cᴴ = 1 := by rw [← conjTranspose_mul, hci, conjTranspose_one]
  show (-T * c⁻¹)ᴴ * Hpk k r + Hpk k r * (-T * c⁻¹) = 0
  have : (-T * c⁻¹)ᴴ * Hpk k r + Hpk k r * (-T * c⁻¹)
      = -((c⁻¹)ᴴ * (cᴴ * Hpk k r * T + Tᴴ * Hpk k r * c) * c⁻¹) := by
    rw [conjTranspose_mul, conjTranspose_neg]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hci']
    simp only [Matrix.mul_assoc, hci, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [this, hz, Matrix.mul_zero, Matrix.zero_mul, neg_zero]
end Formalism.FourierDecayAlt.P.Ux10
