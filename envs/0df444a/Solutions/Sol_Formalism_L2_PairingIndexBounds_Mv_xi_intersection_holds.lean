-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.xi_intersection_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:20:06.701316+00:00
-- url     : https://prove2.me/submissions/d97c954f-9f15-4997-8c3a-8564e9019ee8

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsHeis_WA_add
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsHeis_WB_add
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsHeis_comm
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_Sch_ext
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_rhoA_gen
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_rhoB_gen
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_rhoA_mem
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_rhoB_mem

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
theorem _root_.solution : XiInter := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ θ Xi hXi Φ hΦ
  constructor
  · intro a
    refine ⟨rhoA_mem c A₀ a Φ hΦ, ?_⟩
    have key : Xi ∘ₗ (rhoA a).restrict (rhoA_mem c A₀ a) = WA a ∘ₗ Xi := by
      apply Sch_ext
      intro a' b
      have e : (rhoA a).restrict (rhoA_mem c A₀ a) ⟨gen c A₀ a' b, gen_mem c A₀ a' b⟩
          = ⟨gen c A₀ (a + a') b, gen_mem c A₀ (a + a') b⟩ := Subtype.ext (rhoA_gen c A₀ a a' b)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hXi, e, hXi, hW.WA_add]
    exact LinearMap.congr_fun key ⟨Φ, hΦ⟩
  · intro b
    refine ⟨rhoB_mem c hc A₀ b Φ hΦ, ?_⟩
    have key : Xi ∘ₗ (rhoB c b).restrict (rhoB_mem c hc A₀ b) = WB b ∘ₗ Xi := by
      apply Sch_ext
      intro a b'
      have e : (rhoB c b).restrict (rhoB_mem c hc A₀ b) ⟨gen c A₀ a b', gen_mem c A₀ a b'⟩
          = (c b a)⁻¹ • ⟨gen c A₀ a (b + b'), gen_mem c A₀ a (b + b')⟩ := Subtype.ext (rhoB_gen c hc A₀ b a b')
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hXi, e, map_smul, hXi, hW.WB_add, hW.comm, smul_smul,
        inv_mul_cancel₀ (hc.1 b a), one_smul]
    exact LinearMap.congr_fun key ⟨Φ, hΦ⟩
end Formalism.L2.PairingIndexBounds.Mv
