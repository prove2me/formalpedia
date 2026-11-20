-- Prove2me | solution 1 for DeletionCode.SupportInclusion.hit_component_count_le_of_preimages
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:53.726338+00:00
-- url     : https://prove2.me/submissions/fb916672-7bd1-4639-9db3-c5e1beac926a

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_SupportInclusion
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk

set_option autoImplicit true
open DeletionCode DeletionCode.SupportInclusion
open SignedSupport SupportComponents RuleSetGraph
namespace DeletionCode.SupportInclusion
theorem _root_.solution {L : ℕ}
    {Q S : Finset (Gram L → ℤ)} (hsub : CoordinateSupportIncluded Q S)
    (P : RuleSetComponents S → Prop)
    (hhit : ∀ C, P C → ∃ D, supportComponentMap hsub D = C) :
    Fintype.card {C : RuleSetComponents S // P C} ≤ componentCount Q := by
  classical
  let select : {C : RuleSetComponents S // P C} → RuleSetComponents Q :=
    fun C => Classical.choose (hhit C.val C.property)
  have hselect : ∀ C, supportComponentMap hsub (select C) = C.val :=
    fun C => Classical.choose_spec (hhit C.val C.property)
  have hinj : Function.Injective select := by
    intro C D h
    apply Subtype.ext
    calc
      C.val = supportComponentMap hsub (select C) := (hselect C).symm
      _ = supportComponentMap hsub (select D) := congrArg (supportComponentMap hsub) h
      _ = D.val := hselect D
  have hcard := Fintype.card_le_of_injective select hinj
  simpa only [componentCount, Nat.card_eq_fintype_card] using hcard
end DeletionCode.SupportInclusion
