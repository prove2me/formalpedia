-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.claimD_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:16:56.18243+00:00
-- url     : https://prove2.me/submissions/ee51222d-50c2-4acb-b7df-01ab808a1ab1

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_TorsionKilledCriterionHolds
import Theorems.Thm_Formalism_CoboundaryTransfers_claim_key
import Theorems.Thm_Formalism_CoboundaryTransfers_claim_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
namespace Formalism.CoboundaryTransfers
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : WachMod B M D) (δ : D →ₗ[O] D) (R : Polynomial O) (a k : ℕ) (cΓ : O)
    (h1 : B.PhiX k) (h1' : M ≤ k * (a + 1))
    (h2 : ∀ y, B.X • δ y = W.γ y - y)
    (h3 : ∀ y, W.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W.N)
    (h4 : ∀ y, W.QInv y → (B.p : O) • y ∈ W.N → y ∈ W.N)
    (h6 : ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z')
    (h7 : ∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (a + 1) • n = B.X ^ (a + 1) • z - W.φ (B.X ^ (a + 1) • z)) :
    W.TorsKilled (R.eval 0 * cΓ ^ 2) := by
  intro ω ⟨w, hw, hωw⟩ ⟨j, y, z, hyz, hj⟩
  subst hωw
  have hk := claim_key W δ R a k cΓ h1 h1' h2 h3 h4 h6 w hw j y z hyz hj
  have := claim_fin W δ R a cΓ h2 h6 h7 (cΓ • w) ((QS W).smul_mem _ hw) hk
  have e : (R.eval 0 * cΓ) • (B.X • (cΓ • w)) = (R.eval 0 * cΓ ^ 2) • (B.X • w) := by
    rw [smul_comm B.X cΓ w, smul_smul, pow_two, mul_assoc]
  rwa [e] at this
end Formalism.CoboundaryTransfers
