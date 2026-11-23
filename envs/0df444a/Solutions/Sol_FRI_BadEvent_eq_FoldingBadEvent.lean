-- Prove2me | solution 1 for FRI_BadEvent_eq_FoldingBadEvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:24:48.782472+00:00
-- url     : https://prove2.me/submissions/979925ae-782c-4e1a-9232-7acdf4ed4e4e

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (i : Fin P.num_foldings) (f_prev : FRI_domain P i → F) (alpha : F) :
    FRI_BadEvent P f_0 bound i f_prev alpha ↔
    FoldingBadEvent (FRI_domain P i) (P.m i) (FRI_code P i) (FRI_code_cast P i i.isLt)
      (extend_by_zero (FRI_domain P i) f_prev) (FRI_distance_star P f_0 bound) alpha := by
  simp only [FRI_BadEvent, FoldingBadEvent, FRI_Is_Large_Subset, FRI_code_cast, Fin.eta,
    Fin.is_lt, FRI_domain_succ_eq, ge_iff_le, not_forall, Submodule.mem_map,
    LinearEquiv.funCongrLeft_apply, exists_exists_and_eq_and, LinearMap.funLeft_apply,
    Equiv.subtypeEquiv_apply, Equiv.refl_apply, extend_by_zero, exists_prop]
  simp only [eq_comm]
  exact ⟨fun ⟨S, hS₁, hS₂, hS₃⟩ ↦ ⟨S, hS₁.1, hS₁.2, hS₂, hS₃⟩,
    fun ⟨S, hS₁, hS₂, hS₃, hS₄⟩ ↦ ⟨S, ⟨hS₁, hS₂⟩, hS₃, hS₄⟩⟩
