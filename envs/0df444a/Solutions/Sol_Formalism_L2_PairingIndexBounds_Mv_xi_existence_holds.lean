-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.xi_existence_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:45:35.90988+00:00
-- url     : https://prove2.me/submissions/618cbb8b-d85d-45f8-bd29-f301a695afa3

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_Sch_ext
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_eFam_li
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_gen_eq_eFam
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_W_eq_wFam
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_Sch_le_span_eFam

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
theorem _root_.solution : XiExists := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ θ hA hB
  refine ⟨(Finsupp.linearCombination k (wFam c hc WA WB A₀ θ)) ∘ₗ (eFam_li (k := k) A₀).repr ∘ₗ
    Submodule.inclusion (Sch_le_span_eFam c hc A₀), ?_, ?_⟩
  · intro a b
    have e : Submodule.inclusion (Sch_le_span_eFam c hc A₀) ⟨gen c A₀ a b, gen_mem c A₀ a b⟩
        = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
          (⟨eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b), Submodule.subset_span ⟨_, rfl⟩⟩ :
            Submodule.span k (Set.range (eFam (k := k) A₀))) := by
      apply Subtype.ext
      exact gen_eq_eFam c hc A₀ a b
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e, map_smul, map_smul,
      (eFam_li (k := k) A₀).repr_eq_single ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) _ rfl,
      Finsupp.linearCombination_single, one_smul]
    exact (W_eq_wFam c hc WA WB hW A₀ θ hA hB a b).symm
  · intro Xi' hXi'
    apply Sch_ext
    intro a b
    rw [hXi' a b]
    have e : Submodule.inclusion (Sch_le_span_eFam c hc A₀) ⟨gen c A₀ a b, gen_mem c A₀ a b⟩
        = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
          (⟨eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b), Submodule.subset_span ⟨_, rfl⟩⟩ :
            Submodule.span k (Set.range (eFam (k := k) A₀))) := by
      apply Subtype.ext
      exact gen_eq_eFam c hc A₀ a b
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e, map_smul, map_smul,
      (eFam_li (k := k) A₀).repr_eq_single ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) _ rfl,
      Finsupp.linearCombination_single, one_smul]
    exact W_eq_wFam c hc WA WB hW A₀ θ hA hB a b
end Formalism.L2.PairingIndexBounds.Mv
