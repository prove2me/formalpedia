-- Prove2me | solution 1 for Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:34:04.744132+00:00
-- url     : https://prove2.me/submissions/45ad67ef-7af9-43cd-8cb0-31c61ace95fd

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace Formalism.MainNotions.UnusedSlot33.HK
open NumberField Polynomial Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
variable {R : Ranks} (H : Host R)
private theorem algEquiv_eqOn_K_of_eq_sqd (H : Host R) (σ τ : H.E ≃ₐ[ℚ] H.E) (h : σ H.sqd = τ H.sqd)
    (x : H.E) (hx : x ∈ H.K) : σ x = τ x := by
  have hρ : τ⁻¹ * σ ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd := by
    rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, AlgEquiv.mul_apply, h,
      AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have hle : H.K ≤ IntermediateField.fixedField (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd) := by
    show IntermediateField.adjoin ℚ {H.sqd} ≤ _
    rw [IntermediateField.adjoin_simple_le_iff]
    exact (IntermediateField.mem_fixedField_iff _ _).2 fun f hf => hf
  have h1 := (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) _ hρ
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv] at h1
  calc σ x = τ (τ.symm (σ x)) := (τ.apply_symm_apply _).symm
    _ = τ x := by rw [h1]
private theorem algEquiv_fix_K_of_gal_eq_one (H : Host R) (σ : H.E ≃ₐ[ℚ] H.E) (h : (H.gal σ).1.2 = 1)
    (x : H.E) (hx : x ∈ H.K) : σ x = x := by
  have h1 := algEquiv_eqOn_K_of_eq_sqd H σ 1 (by rw [H.gal_sqd, h, AlgEquiv.one_apply]; simp) x hx
  rwa [AlgEquiv.one_apply] at h1
end Formalism.MainNotions.UnusedSlot33.HK
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.UnusedSlot33 Formalism.MainNotions.UnusedSlot33.HK
open NumberField Polynomial Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
variable {R : Ranks} (H : Host R)
namespace Formalism.MainNotions.UnusedSlot33.HK
theorem _root_.solution (g : R.GG) (hg : g ∈ R.Psi) (x : H.E) (hx : x ∈ H.K) :
    H.sigmaOf g x = x := by
  have hk : R.toFrame.chD g = 1 := MonoidHom.mem_ker.1 (show g ∈ R.toFrame.chD.ker from hg)
  have hg' : g.1.2 = 1 := by simpa [Formalism.HC.Frame.chD] using hk
  refine algEquiv_fix_K_of_gal_eq_one H (H.sigmaOf g) ?_ x hx
  rw [show H.gal (H.sigmaOf g) = g from H.gal.apply_symm_apply g]
  exact hg'
end Formalism.MainNotions.UnusedSlot33.HK
