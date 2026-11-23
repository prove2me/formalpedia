-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.phase_locally_constant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:10.720782+00:00
-- url     : https://prove2.me/submissions/21afab6e-48bd-4a33-8757-89afb0c84b65

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_Kp_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_det_addBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_inv_mem_of_near
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_inv_bdd
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_mulR
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.KernelScalingBack
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.LocConst := by
  intro K _ _ _ R ψ hD _ s h Om hs hOm hU
  obtain ⟨ϖ, hϖ, hu⟩ := hD.unif
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => A5x3.psi_of_mem hD.selfDual hr
  obtain ⟨N, hN⟩ := inv_bdd R hD.isOpen ϖ hϖ hu Om hOm hU
  obtain ⟨c0, hc0⟩ := det_addBlock h s
  obtain ⟨N0, hN0⟩ := hu ((c0⁻¹ : Kˣ) : K)
  have hlat := A5x5.lat_mulR hD.isOpen hD.isCompact (ϖ ^ (1 + N + N0 + s * N))
  refine ⟨mulR R ((ϖ ^ (1 + N + N0 + s * N) : Kˣ) : K), ⟨hlat.op, hlat.cp⟩, ?_⟩
  intro z z' hz hl w'
  obtain ⟨r, hr, hrl⟩ := hl
  have hr' : r ∈ R := hr
  have hrl' : (ϖ : K) ^ (1 + N + N0 + s * N) * r = (z' : K) - (z : K) := by
    rw [← hrl]; simp
  have hy := hN z hz
  have hzy : (z : K) * ((z⁻¹ : Kˣ) : K) = 1 := Units.mul_inv z
  have hk1 : ((z⁻¹ * z' : Kˣ) : K) = 1 + (ϖ : K) *
      ((ϖ : K) ^ (N0 + s * N) * r * ((ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K))) := by
    rw [Units.val_mul]
    have e : (ϖ : K) ^ (1 + N + N0 + s * N) = (ϖ : K) * (ϖ : K) ^ (N0 + s * N) * (ϖ : K) ^ N := by
      ring
    rw [e] at hrl'
    linear_combination (-((z⁻¹ : Kˣ) : K)) * hrl' + hzy
  have hρ : (ϖ : K) ^ (N0 + s * N) * r * ((ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K)) ∈ R :=
    R.mul_mem (R.mul_mem (R.pow_mem hϖ _) hr') hy
  have hk : ((z⁻¹ * z' : Kˣ) : K) ∈ R := by
    rw [hk1]; exact R.add_mem R.one_mem (R.mul_mem hϖ hρ)
  have hki : (((z⁻¹ * z')⁻¹ : Kˣ) : K) ∈ R := inv_mem_of_near R ϖ hϖ hu _ _ hρ hk1
  have hkk : ((z⁻¹ * z' : Kˣ) : K) * (((z⁻¹ * z')⁻¹ : Kˣ) : K) = 1 := Units.mul_inv _
  have hinv : Ring.inverse (pt (addBlock h s z).1 (addBlock h s z).2).det =
      ((c0⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) ^ s := by
    rw [hc0, Ring.inverse_unit, mul_inv, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val]
  have hzk : z' = z * (z⁻¹ * z') := by group
  have hkz : ((z⁻¹ * z' : Kˣ) : K) = ((z⁻¹ : Kˣ) : K) * (z' : K) := Units.val_mul _ _
  rw [hzk]
  refine Kp_block R ψ hψ h s hs z (z⁻¹ * z') hk hki ?_ ?_ w'
  · rw [hinv]
    have e : ((((z⁻¹ * z')⁻¹ : Kˣ) : K) - 1) * (((c0⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) ^ s) =
        -(((z⁻¹ * z')⁻¹ : Kˣ) : K) * ((ϖ : K) * r * ((ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K)) *
          ((ϖ : K) ^ N0 * ((c0⁻¹ : Kˣ) : K)) * ((ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K)) ^ s) := by
      have e1 : (ϖ : K) ^ (1 + N + N0 + s * N) = (ϖ : K) * (ϖ : K) ^ N * (ϖ : K) ^ N0 *
          ((ϖ : K) ^ N) ^ s := by ring
      rw [e1] at hrl'
      rw [hkz] at hkk
      rw [mul_pow]
      linear_combination (((c0⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) ^ s) * hkk +
        ((((z⁻¹ * z')⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) * ((c0⁻¹ : Kˣ) : K) *
          ((z⁻¹ : Kˣ) : K) ^ s) * hrl' -
        ((((z⁻¹ * z')⁻¹ : Kˣ) : K) * ((c0⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) ^ s) * hzy
    rw [e]
    exact R.mul_mem (R.neg_mem hki) (R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem hϖ hr') hy) hN0)
      (R.pow_mem hy s))
  · rw [hinv]
    have e : (((z⁻¹ * z' : Kˣ) : K) - 1) * (z : K) * (((c0⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) ^ s) =
        (ϖ : K) ^ (1 + N) * r * ((ϖ : K) ^ N0 * ((c0⁻¹ : Kˣ) : K)) *
          ((ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K)) ^ s := by
      have e1 : (ϖ : K) ^ (1 + N + N0 + s * N) = (ϖ : K) ^ (1 + N) * (ϖ : K) ^ N0 *
          ((ϖ : K) ^ N) ^ s := by ring
      rw [e1] at hrl'
      rw [hkz, mul_pow]
      linear_combination ((z' : K) * ((c0⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) ^ s) * hzy -
        (((c0⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) ^ s) * hrl'
    rw [e]
    exact R.mul_mem (R.mul_mem (R.mul_mem (R.pow_mem hϖ _) hr') hN0) (R.pow_mem hy s)
end Formalism.FourierDecayAlt.P
