-- Prove2me | solution 1 for Formalism.L2.Th1.H.ud_isQuadFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:48:34.955163+00:00
-- url     : https://prove2.me/submissions/f0e30cfe-e94a-4db2-861d-a4a1c03d5335

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
import Theorems.Thm_Formalism_L2_Th1_H_ud_norm
import Theorems.Thm_Formalism_L2_Th1_H_ud_phi_add
import Theorems.Thm_Formalism_L2_Th1_H_bC_add_left
import Theorems.Thm_Formalism_L2_Th1_H_ud_radical
import Theorems.Thm_Formalism_L2_Th1_H_ud_phi_nsmul
import Theorems.Thm_Formalism_L2_Th1_H_phiQ_mk
import Theorems.Thm_Formalism_L2_Th1_H_bQ_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ}
  {δ Ae : V ≃ₗ[ℂ] V}
namespace Formalism.L2.Th1.H
theorem _root_.solution (h : UnitaryData H Λ α δ Ae) : IsQuadFn (phiQ H Λ α δ Ae) (bQ H Λ δ Ae) where
  add := by
    intro c d
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      induction d using QuotientAddGroup.induction_on with
      | H y =>
        rw [← QuotientAddGroup.mk_add, phiQ_mk h, phiQ_mk h, phiQ_mk h, bQ_mk h]
        exact ud_phi_add h x.2 y.2
  left := by
    intro c d e
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      induction d using QuotientAddGroup.induction_on with
      | H y =>
        induction e using QuotientAddGroup.induction_on with
        | H z =>
          rw [← QuotientAddGroup.mk_add, bQ_mk h, bQ_mk h, bQ_mk h]
          exact bC_add_left _ _ _
  sq := by
    intro k c
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      rw [← QuotientAddGroup.mk_nsmul, phiQ_mk h, phiQ_mk h]
      exact ud_phi_nsmul h x.2 k
  ne := by
    intro c
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      rw [phiQ_mk h]
      intro h0
      have := ud_norm h x.2
      rw [h0, norm_zero] at this
      exact zero_ne_one this
  nondeg := by
    intro c hc
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      refine ud_radical h x.2 fun x' hx' => ?_
      have := hc (QuotientAddGroup.mk (⟨x', hx'⟩ : Λ))
      rwa [bQ_mk h] at this
end Formalism.L2.Th1.H
