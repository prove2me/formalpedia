-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.relIndex_eq_card_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:47:43.962572+00:00
-- url     : https://prove2.me/submissions/5df38fc7-54b4-4344-87ba-7dc50e922ab4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeMemOfMemSmulTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {G α : Type*} [Group G] (H S : Subgroup G) (f : G → α)
    (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b ↔ a⁻¹ * b ∈ H) :
    H.relIndex S = Nat.card {c : α // ∃ a ∈ S, f a = c} := by
  classical
  show Nat.card (S ⧸ H.subgroupOf S) = _
  apply Nat.card_congr
  refine Equiv.ofBijective (fun q => Quotient.liftOn' q
    (fun a : S => (⟨f a, a, a.2, rfl⟩ : {c : α // ∃ a ∈ S, f a = c})) ?_) ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    show f a = f b
    have hab' : a⁻¹ * b ∈ H.subgroupOf S := QuotientGroup.leftRel_apply.mp hab
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hab'
    exact (hf a a.2 b b.2).mpr hab'
  · intro q₁ q₂ e
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
    induction q₂ using QuotientGroup.induction_on with
    | H b =>
    have e' : f a = f b := congrArg Subtype.val e
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (hf a a.2 b b.2).mp e'
  · rintro ⟨c, a, ha, rfl⟩
    exact ⟨QuotientGroup.mk ⟨a, ha⟩, rfl⟩
end Formalism.HermitianLattices.Ext.L3.D2
