-- Prove2me | solution 1 for Formalism.L2.Th1.H.bQ_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:12:26.113841+00:00
-- url     : https://prove2.me/submissions/4cd3bf42-b948-4a15-9e47-13a2600654b5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
import Theorems.Thm_Formalism_L2_Th1_H_ud_b_symm
import Theorems.Thm_Formalism_L2_Th1_H_bC_add_left
import Theorems.Thm_Formalism_L2_Th1_H_ud_latA_le
import Theorems.Thm_Formalism_L2_Th1_H_ud_radical_of_mem
import Theorems.Thm_Formalism_L2_Th1_H_out_mk_latA

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
theorem _root_.solution (h : UnitaryData H Λ α δ Ae) (x y : Λ) :
    bQ H Λ δ Ae (QuotientAddGroup.mk x) (QuotientAddGroup.mk y) = bC H Ae x y := by
  unfold bQ
  obtain ⟨k, hk, hek⟩ := out_mk_latA (δ := δ) (Ae := Ae) x
  obtain ⟨k', hk', hek'⟩ := out_mk_latA (δ := δ) (Ae := Ae) y
  rw [hek, hek']
  have hk'Λ := ud_latA_le h hk'
  have hyk : (y : V) + k' ∈ Λ := Λ.add_mem y.2 hk'Λ
  rw [bC_add_left, ud_radical_of_mem h hk hyk, mul_one, ud_b_symm h x.2 hyk, bC_add_left,
    ud_radical_of_mem h hk' x.2, mul_one, ud_b_symm h y.2 x.2]
end Formalism.L2.Th1.H
