-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.isoTransfer_proof2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:23:55.90684+00:00
-- url     : https://prove2.me/submissions/259e43b0-9141-4ca9-8958-c14d2ef339ad

import Definitions.Def_Formalism_LogSumExpBounds_StatementC
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DescEquivLiftEquiv
import Theorems.Thm_P2M_Formalism_NuclearRankWeightBounds_P_PB___bbar_e0c4441375c8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Formalism.NuclearRankWeightBounds.C
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution : Formalism.NuclearRankWeightBounds.C.IsoTransfer := by
  intro RR K _ _ _ hinj m₁ m₂ Z₁ Z₂ h1 h2 h1' h2' hκ
  have hc : cval K Z₁ = cval K Z₂ := by
    have e1 := cval_mul_kappa Z₁ h1 h1'
    have e2 := cval_mul_kappa Z₂ h2 h2'
    rw [hκ] at e1
    calc cval K Z₁ = cval K Z₁ * (cval K Z₂ * kappa K Z₂) := by rw [e2, mul_one]
      _ = cval K Z₂ * (cval K Z₁ * kappa K Z₂) := by ring
      _ = cval K Z₂ := by rw [e1, mul_one]
  have eA := (PA Z₁ h1).isoEquiv (PA Z₂ h2) hinj (Submodule.Quotient.mk eN)
    (Submodule.Quotient.mk eN)
    (by
      change fV Z₁ eN = fV Z₂ eN
      rw [show fV (K := K) Z₁ eN = kappa K Z₁ from fV_single Z₁,
        show fV (K := K) Z₂ eN = kappa K Z₂ from fV_single Z₂, hκ])
  have eB := (PB Z₁ h1 h1').isoEquiv (PB Z₂ h2 h2') hinj (Submodule.Quotient.mk (Z₁ *ᵥ eN))
    (Submodule.Quotient.mk (Z₂ *ᵥ eN))
    (by
      change -(cval K Z₁) * fV Z₁ (Z₁ *ᵥ eN) = -(cval K Z₂) * fV Z₂ (Z₂ *ᵥ eN)
      rw [fV_mulVec Z₁ h1, fV_mulVec Z₂ h2, hc]
      simp [eN])
  have eA' : {θ : coker Z₁ ≃ₗ[RR] coker Z₂ //
      θ (ebar Z₁) = ebar Z₂ ∧ (lam K Z₂).comp θ.toLinearMap = lam K Z₁} ≃ _ := eA
  have eB' : _ ≃ {θ : coker (blk Z₁) ≃ₗ[RR] coker (blk Z₂) //
      θ (bbar Z₁) = bbar Z₂ ∧ (alpha K Z₂).comp θ.toLinearMap = alpha K Z₁} :=
    eB.symm.trans (Equiv.subtypeEquivRight fun θ => by
      rw [PB_π_bbar, PB_π_bbar]; rfl)
  exact ⟨eA'.trans ((midEquiv Z₁ Z₂ h1 h2 h1' h2' hc).trans eB')⟩
end Formalism.NuclearRankWeightBounds.P
