-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hermitian_standard_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:31.297313+00:00
-- url     : https://prove2.me/submissions/ac240362-bee6-4603-ae63-da31cddfe705

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_trace_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_trace_surj
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hB_add_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hB_add_right
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hB_conj
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_exists_orth_family_gen
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_norm_surj
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hB_smul_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hB_smul_right
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : HermStdForm := by
  intro K L _ _ _ _ _ h2 n Ph hPh hherm
  classical
  let _ : StarRing L := frobStar h2
  let h : (Fin n → L) →ₗ[L] (Fin n → L) →ₗ⋆[L] L :=
    LinearMap.mk₂'ₛₗ (RingHom.id L) (starRingEnd L) (fun x y => hB K Ph x y)
      (hB_add_left Ph) (fun c x y => hB_smul_left Ph c x y) (hB_add_right Ph)
      (fun c x y => hB_smul_right Ph c x y)
  have hh : ∀ x y, h x y = hB K Ph x y := fun x y => rfl
  have hH : IsHerm h := fun v w => (hB_conj Ph h2 hherm v w).symm
  have hSD : SelfDual h := by
    refine ⟨hH, fun φ => ?_⟩
    let f : Fin n → L := fun k => φ (fun j => if k = j then 1 else 0)
    refine ⟨fun l => (Ph⁻¹.mulVec f l) ^ Fintype.card K, fun v => ?_⟩
    rw [hh, LinearMap.pi_apply_eq_sum_univ φ v]
    simp only [hB, frob_frob h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : ∑ l, Ph k l * Ph⁻¹.mulVec f l = f k := by
      have : Ph.mulVec (Ph⁻¹.mulVec f) = f := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Ph hPh, Matrix.one_mulVec]
      exact congrFun this k
    rw [smul_eq_mul]
    change v k * f k = _
    rw [← e1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  obtain ⟨θ, hθ⟩ := trace_surj (K := K) (L := L) 1
  have hθ' : θ + θ ^ Fintype.card K = 1 := by rw [← trace_eq h2, hθ, map_one]
  have hpol : ∀ C : Submodule L (Fin n → L), (∀ c ∈ C, ¬ IsUnit (h c c)) →
      ∀ c ∈ C, ∀ c' ∈ C, h c c' ∈ (⊥ : Ideal L) := by
    intro C hC c hc c' hc'
    have h0 : ∀ x ∈ C, hB K Ph x x = 0 := fun x hx => by
      by_contra hne
      exact hC x hx (isUnit_iff_ne_zero.2 hne)
    rw [Ideal.mem_bot, hh]
    by_contra hz
    have e1 := h0 _ (C.add_mem (C.smul_mem (θ / hB K Ph c c') hc) hc')
    rw [hB_add_left, hB_add_right, hB_add_right, h0 _ (C.smul_mem _ hc), h0 _ hc',
      ← hB_conj Ph h2 hherm ((θ / hB K Ph c c') • c) c', hB_smul_left, div_mul_cancel₀ _ hz] at e1
    rw [zero_add, add_zero, hθ'] at e1
    exact one_ne_zero e1
  obtain ⟨v, horth, hunit⟩ := exists_orth_family_gen h ⊥
    (fun x hx => by rw [Ideal.mem_bot] at hx; rw [hx]; exact not_isUnit_zero) hpol hSD n
    (by rw [Module.finrank_fin_fun])
  have hlam : ∀ i, ∃ lam : L, lam ^ (Fintype.card K + 1) = (hB K Ph (v i) (v i))⁻¹ := by
    intro i
    have hne : hB K Ph (v i) (v i) ≠ 0 := (hunit i).ne_zero
    exact norm_surj h2 _ (inv_ne_zero hne) (by rw [inv_pow, hB_conj Ph h2 hherm])
  choose lam hlam using hlam
  let A : Matrix (Fin n) (Fin n) L := Matrix.of fun i k => lam i * v i k
  have hA : A * Ph * (A.map fun y => y ^ Fintype.card K).transpose = 1 := by
    ext i i'
    have e1 : (A * Ph * (A.map fun y => y ^ Fintype.card K).transpose) i i'
        = hB K Ph (lam i • v i) (lam i' • v i') := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, A, Matrix.of_apply, hB,
        Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      exact Finset.sum_comm
    rw [e1, hB_smul_left, hB_smul_right, Matrix.one_apply]
    split_ifs with hii
    · subst hii
      have hne : hB K Ph (v i) (v i) ≠ 0 := (hunit i).ne_zero
      rw [← mul_assoc, ← pow_succ', hlam, inv_mul_cancel₀ hne]
    · have : hB K Ph (v i) (v i') = 0 := horth i i' hii
      rw [this, mul_zero, mul_zero]
  refine ⟨A, ?_, hA⟩
  have := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one, mul_assoc] at this
  exact IsUnit.of_mul_eq_one _ this
end Formalism.HermitianLatticeCounting.P.S4aux
