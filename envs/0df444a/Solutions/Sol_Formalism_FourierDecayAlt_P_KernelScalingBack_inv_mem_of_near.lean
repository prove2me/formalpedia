-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.inv_mem_of_near
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:37.341801+00:00
-- url     : https://prove2.me/submissions/4dc35433-f8ea-4f49-8a02-457826d5b83d

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution (ϖ : K) (hϖ : ϖ ∈ R) (hu : ∀ x : K, ∃ m : ℕ, ϖ ^ m * x ∈ R) (x : Kˣ)
    (r : K) (hr : r ∈ R) (hx : (x : K) = 1 + ϖ * r) : ((x⁻¹ : Kˣ) : K) ∈ R := by
  have hy : ((x⁻¹ : Kˣ) : K) = 1 - ϖ * r * ((x⁻¹ : Kˣ) : K) := by
    have := Units.mul_inv x
    rw [hx] at this
    linear_combination this
  have key : ∀ m : ℕ, ϖ ^ m * ((x⁻¹ : Kˣ) : K) ∈ R → ((x⁻¹ : Kˣ) : K) ∈ R := by
    intro m
    induction m with
    | zero => intro h; simpa using h
    | succ m ih =>
      intro h
      apply ih
      have e : ϖ ^ m * ((x⁻¹ : Kˣ) : K) = ϖ ^ m - r * (ϖ ^ (m + 1) * ((x⁻¹ : Kˣ) : K)) := by
        rw [pow_succ]
        linear_combination ϖ ^ m * hy
      rw [e]
      exact R.sub_mem (R.pow_mem hϖ m) (R.mul_mem hr h)
  obtain ⟨m, hm⟩ := hu ((x⁻¹ : Kˣ) : K)
  exact key m hm
end Formalism.FourierDecayAlt.P.KernelScalingBack
