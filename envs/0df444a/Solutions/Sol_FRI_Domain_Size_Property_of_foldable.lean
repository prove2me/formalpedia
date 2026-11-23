-- Prove2me | solution 1 for FRI_Domain_Size_Property_of_foldable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:36:43.062299+00:00
-- url     : https://prove2.me/submissions/f8df6c85-d72a-4ee1-a44a-198b123347d6

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_FRI_domain_foldable
import Theorems.Thm_foldable_pow_domain_card


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) : FRI_Domain_Size_Property P := by
  intro i h
  rw [FRI_domain_succ_eq, foldable_pow_domain_card (FRI_domain P i) (P.m ⟨i, h⟩)
    (FRI_domain_foldable P ⟨i, h⟩)]
