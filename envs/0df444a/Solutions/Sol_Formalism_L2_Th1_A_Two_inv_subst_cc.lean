-- Prove2me | solution 1 for Formalism.L2.Th1.A.Two.inv_subst_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:20:26.717837+00:00
-- url     : https://prove2.me/submissions/667848ec-0b7f-4f84-87ce-2efe3fb2acfc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
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


section
open PowerSeries
universe u
noncomputable section
namespace Formalism.L2.Th1.A
namespace Two
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
private theorem cc_subst_lemma {R : Type*} [CommRing R] {e : R⟦X⟧} (he : HasSubst e)
    (he0 : constantCoeff e = 0) (f : R⟦X⟧) : constantCoeff (f.subst e) = constantCoeff f := by
  have hC : (C (constantCoeff f) : R⟦X⟧).subst e = C (constantCoeff f) := by
    rw [← PowerSeries.coe_substAlgHom he]
    exact (PowerSeries.substAlgHom he).commutes _
  conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const f]
  rw [← PowerSeries.coe_substAlgHom he, map_add, map_mul, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X he, hC, map_add, map_mul, he0, mul_zero, zero_add, PowerSeries.constantCoeff_C]
end Two
open Two
namespace Two
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
end Two
end Formalism.L2.Th1.A
end
end

set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Two
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
namespace Formalism.L2.Th1.A.Two
theorem _root_.solution (xP : K) :
    constantCoeff ((invOfUnit (tDen W xP) 1).subst (expSer W)) = 1 := by
  have hc : constantCoeff (tDen W xP) = 1 := by
    simp [tDen, xS, PowerSeries.constantCoeff_invOfUnit]
  have hm : tDen W xP * invOfUnit (tDen W xP) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simpa using hc)
  have h1 : (tDen W xP).subst (expSer W) * (invOfUnit (tDen W xP) 1).subst (expSer W) = 1 := by
    rw [← PowerSeries.coe_substAlgHom (he W), ← map_mul, hm, map_one]
  have h2 := congrArg constantCoeff h1
  rw [map_mul, map_one, cc_subst_lemma (he W) (e0 W) (tDen W xP), hc, one_mul] at h2
  exact h2
end Formalism.L2.Th1.A.Two
