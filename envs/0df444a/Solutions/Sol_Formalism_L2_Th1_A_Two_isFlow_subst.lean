-- Prove2me | solution 1 for Formalism.L2.Th1.A.Two.isFlow_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:26:04.240167+00:00
-- url     : https://prove2.me/submissions/2db0ec7d-3846-4994-ad22-f0f8c31ca9ca

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_chainZ
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Two
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
namespace Formalism.L2.Th1.A.Two
theorem _root_.solution {a b : K⟦X⟧} (h : IsFlow (curveS W) (D W) a b) :
    IsFlow (curveS W) (derivative K) (a.subst (expSer W)) (b.subst (expSer W)) := by
  obtain ⟨hE, hDa, hDb⟩ := h
  have hφ : ∀ f : K⟦X⟧, f.subst (expSer W) = PowerSeries.substAlgHom (he W) f := fun f => by
    rw [PowerSeries.coe_substAlgHom]
  have hC : ∀ c : K, PowerSeries.substAlgHom (he W) (C c) = C c := fun c =>
    (PowerSeries.substAlgHom (he W)).commutes c
  refine ⟨?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff] at hE ⊢
    have h2 := congrArg (PowerSeries.substAlgHom (he W)) hE
    simp only [map_add, map_mul, map_pow, curveS, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, hC] at h2 ⊢
    rw [hφ, hφ]
    exact h2
  · rw [chainZ K W, hDa]
    simp only [hφ, map_add, map_mul, map_ofNat, curveS, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, hC]
  · rw [chainZ K W, hDb]
    simp only [hφ, map_add, map_sub, map_mul, map_pow, map_ofNat, curveS, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, hC]
end Formalism.L2.Th1.A.Two
