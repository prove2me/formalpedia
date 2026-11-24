-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.intPS_compInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:40:15.41318+00:00
-- url     : https://prove2.me/submissions/8360e52c-52d5-4f65-94cf-bfb3f7045318

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_compInvMap
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
noncomputable section
open Formalism Formalism.L2 Formalism.L2.KerInert Formalism.L2.KerInert.VC
open Formalism.L2.Th1.A
open Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] (R' : Subring K)
namespace Formalism.L2.KerInert.VC
theorem _root_.solution {f : K⟦X⟧} (hf : IntPS R' f) (h0 : constantCoeff f = 0) {u ui : K} (hui : ui ∈ R')
    (h1 : coeff 1 f = u) (huu : u * ui = 1) : IntPS R' (compInv f) := by
  let fS : R'⟦X⟧ := PowerSeries.mk fun n => ⟨coeff n f, hf n⟩
  have e : PowerSeries.map R'.subtype fS = f := by
    ext n; simp [fS]
  have h0S : constantCoeff fS = 0 := by
    apply Subtype.ext
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [fS, h0]
  have hm : coeff 1 fS * ⟨ui, hui⟩ = 1 := Subtype.ext (by simp [fS, h1, huu])
  have h1S : IsUnit (coeff 1 fS) := ⟨⟨_, ⟨ui, hui⟩, hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  intro n
  rw [← e, ← compInvMap R' K R'.subtype fS h0S h1S, coeff_map]
  exact SetLike.coe_mem _
end Formalism.L2.KerInert.VC
