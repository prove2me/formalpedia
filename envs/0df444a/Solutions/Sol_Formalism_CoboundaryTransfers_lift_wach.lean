-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.lift_wach
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:38:16.171294+00:00
-- url     : https://prove2.me/submissions/8bc9e7e0-877b-445d-8d5c-f5fa0dd52ae1

import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_GammaStableOfGammaQUnitHolds
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_DiffOneSmulOfTower
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_TorsionKilledCriterionHolds
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_BridgeCL
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_BridgeLIFT
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_DepthPageFirstZetaFactorEqPrimePower
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_Transfer
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_WachLatticeNonemptyGamma
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_IntegralWachDefinitions
import Definitions.Def_Formalism_CoboundaryTransfers_WachBridges
import Theorems.Thm_Formalism_CL_W_gammaImageProduct_holds
import Theorems.Thm_Formalism_CoboundaryTransfers_cocycleLiftOfExact_holds
import Theorems.Thm_Formalism_CoboundaryTransfers_gammaImageProduct_holds
import Theorems.Thm_Formalism_CoboundaryTransfers_torsionKilledCriterion_holds


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
namespace Formalism.CoboundaryTransfers
theorem _root_.solution (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (e : ℕ) (hW : CokerKilled S e) (hQ : RatSurj S)
    (δ : D₀ →ₗ[O] D₀) (R : Polynomial O) (a k : ℕ) (u : O)
    (hk : B.PhiX k) (ha : M ≤ k * (a + 1))
    (hδ : ∀ y, B.X • δ y = W₀.γ y - y)
    (hR : ∀ y, W₀.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W₀.N)
    (hZ : ∀ y, W₀.QInv y → (B.p : O) • y ∈ W₀.N → y ∈ W₀.N)
    (hZu : ∀ y, W₀.QInv y → (∏ i ∈ Finset.Icc 1 a, (1 - u ^ i)) • y ∈ W₀.N → y ∈ W₀.N)
    (hgr : ∀ i, 1 ≤ i → i ≤ a → ∀ n ∈ W₀.N, ∃ n' ∈ W₀.N,
      W₀.γ (B.X ^ i • n) = u ^ i • (B.X ^ i • n) + B.X ^ (i + 1) • n')
    (hφ : ∀ n ∈ W₀.N, ∃ z ∈ W₀.N,
      B.X ^ (a + 1) • n = B.X ^ (a + 1) • z - W₀.φ (B.X ^ (a + 1) • z)) :
    Lifts S ((B.p : O) ^ e * (R.eval 0 * ∏ i ∈ Finset.Icc 1 a, (1 - u ^ i))) :=
  cocycleLiftOfExact_holds O A B M D₀ D₁ D₂ W₀ W₁ W₂ S e _ hW hQ
    (torsionKilledCriterion_holds O A B M D₀ W₀ δ R a k _ hk ha hδ hR hZ hZu
      (gammaImageProduct_holds O A B M D₀ W₀ u a hgr) hφ)
end Formalism.CoboundaryTransfers
