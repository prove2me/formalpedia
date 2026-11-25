-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.IA.relIndex_eq_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:59:48.461684+00:00
-- url     : https://prove2.me/submissions/6b059dd2-3851-4146-b7a3-f3069181a083

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SurjectiveOfNondegenerate
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2 Formalism.HermitianLattices.Ext.L3.D2.IA
namespace Formalism.HermitianLattices.Ext.L3.D2.IA
theorem _root_.solution {G M : Type*} [Group G] [AddCommGroup M] (H T : Subgroup G)
    (N' N : AddSubgroup M) (f : G → M) (hf : ∀ X ∈ T, f X ∈ N)
    (hc : ∀ X ∈ T, ∀ Y ∈ T, X⁻¹ * Y ∈ H ↔ f X - f Y ∈ N')
    (hsurj : ∀ Z ∈ N, ∃ X ∈ T, f X - Z ∈ N') : H.relIndex T = N'.relIndex N := by
  unfold Subgroup.relIndex AddSubgroup.relIndex Subgroup.index AddSubgroup.index
  let g : (T ⧸ H.subgroupOf T) → (N ⧸ N'.addSubgroupOf N) :=
    Quotient.lift (s := QuotientGroup.leftRel (H.subgroupOf T))
      (fun X : T => ((⟨f X, hf X X.2⟩ : N) : N ⧸ N'.addSubgroupOf N)) (by
        intro X Y hXY
        have hXY := QuotientGroup.leftRel_apply.1 hXY
        have h1 : f X - f Y ∈ N' := (hc X X.2 Y Y.2).1 (by simpa [Subgroup.mem_subgroupOf] using hXY)
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        have := N'.neg_mem h1
        simpa [neg_add_eq_sub] using this)
  refine Nat.card_eq_of_bijective g ⟨?_, ?_⟩
  · intro a b
    induction a using QuotientGroup.induction_on with | _ X => ?_
    induction b using QuotientGroup.induction_on with | _ Y => ?_
    intro hab
    have h1 : ((⟨f X, hf X X.2⟩ : N) : N ⧸ N'.addSubgroupOf N) = ((⟨f Y, hf Y Y.2⟩ : N) : N ⧸ N'.addSubgroupOf N) := hab
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h2 : f X - f Y ∈ N' := by
      have := N'.neg_mem h1
      simpa [neg_add_eq_sub] using this
    simpa using (hc X X.2 Y Y.2).2 h2
  · intro b
    induction b using QuotientAddGroup.induction_on with | _ Z => ?_
    obtain ⟨X, hX, hXZ⟩ := hsurj Z Z.2
    refine ⟨((⟨X, hX⟩ : T) : T ⧸ H.subgroupOf T), ?_⟩
    show ((⟨f X, hf X hX⟩ : N) : N ⧸ N'.addSubgroupOf N) = (Z : N ⧸ N'.addSubgroupOf N)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have := N'.neg_mem hXZ
    simpa [neg_add_eq_sub] using this
end Formalism.HermitianLattices.Ext.L3.D2.IA
