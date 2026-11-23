-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.gen_eq_eFam
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:19.748409+00:00
-- url     : https://prove2.me/submissions/61aa54dc-0459-4a7f-b72c-309269155171

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_ind_of_mem
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_ind_of_not_mem
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_gen_apply
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_chi_apply
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_eFam_of_mem
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_eFam_of_not_mem
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_out_sub_mem

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
theorem _root_.solution (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (a : A) (b : B) :
    gen c A₀ a b = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
      eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) := by
  funext t
  have h0 := out_sub_mem A₀ a
  rw [gen_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : t + (QuotientAddGroup.mk a : A ⧸ A₀).out ∈ A₀
  · have h' : t + a ∈ A₀ := by
      have := A₀.add_mem h h0
      have e : t + (QuotientAddGroup.mk a : A ⧸ A₀).out + (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) = t + a := by abel
      rwa [e] at this
    rw [ind_of_mem (show t + a ∈ (A₀ : Set A) from h'), mul_one,
      eFam_of_mem A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) t h, chi_apply, ← hc.2.2]
    congr 1
    change t + a = a - (QuotientAddGroup.mk a : A ⧸ A₀).out + (t + (QuotientAddGroup.mk a : A ⧸ A₀).out)
    abel
  · have h' : t + a ∉ (A₀ : Set A) := by
      intro h'
      apply h
      have := A₀.sub_mem h' h0
      have e : t + a - (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) = t + (QuotientAddGroup.mk a : A ⧸ A₀).out := by abel
      rwa [e] at this
    rw [ind_of_not_mem h', eFam_of_not_mem A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) t h, mul_zero, mul_zero]
end Formalism.L2.PairingIndexBounds.Mv
