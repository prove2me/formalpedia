-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.lattice_moves_hold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:28:39.468111+00:00
-- url     : https://prove2.me/submissions/2d669c6a-365c-451e-85ce-860577b611ff

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_model_moves_hold
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_Xi_of_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
namespace Formalism.L2.PairingIndexBounds.Mv
theorem _root_.solution : Moves := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ A₁ B₀ B₁ θ Xi hXi hB₀ h11 hA SA SB hSA hSB hcard
  have hM : ∑ a ∈ SA, ∑ b ∈ SB, gen c A₀ a b = (SB.card : k) • ind (A₁ : Set A) :=
    model_moves_hold k A B c hc A₀ A₁ B₀ B₁ hB₀ h11 hA SA SB hSA hSB
  have hexp : ind (A₁ : Set A) = ∑ i ∈ SA ×ˢ SB, (SB.card : k)⁻¹ • gen c A₀ i.1 i.2 := by
    rw [← Finset.smul_sum, Finset.sum_product, hM, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  obtain ⟨h, hval⟩ := Xi_of_eq_sum hXi (SA ×ˢ SB) (fun _ => (SB.card : k)⁻¹) Prod.fst Prod.snd _ hexp
  refine ⟨h, ?_⟩
  rw [hval, ← Finset.smul_sum, smul_smul, mul_inv_cancel₀ hcard, one_smul, Finset.sum_product]
end Formalism.L2.PairingIndexBounds.Mv
