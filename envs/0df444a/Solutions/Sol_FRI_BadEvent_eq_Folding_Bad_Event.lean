-- Prove2me | solution 1 for FRI_BadEvent_eq_Folding_Bad_Event
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:22:14.101042+00:00
-- url     : https://prove2.me/submissions/722b1ceb-c2dd-42fa-896f-9ac3b958bf31

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (i : Fin P.num_foldings) (f_prev : FRI_domain P i → F) (alpha : F) :
    FRI_BadEvent P f_0 bound i f_prev alpha ↔
    Folding_Bad_Event (FRI_domain P i) (P.m i) (FRI_degree P i)
      f_prev alpha (FRI_distance_star P f_0 bound) := by
  constructor
  · rintro ⟨S, hS₁, hS₂⟩
    refine ⟨S, hS₁.1, ?_, ?_⟩
    · convert hS₁.2 using 1
      rw [FRI_domain_succ_eq P i i.2]
    · convert hS₂ using 1
      · simp only [FRI_code]
        rw [FRI_domain_succ_eq P i i.2]
        simp [FRI_degree]
      · rfl
  · rintro ⟨S, hS₁, hS₂, hS₃⟩
    refine ⟨S, ⟨hS₁, ?_⟩, ?_⟩
    · convert hS₂ using 1
      rw [FRI_domain_succ_eq P i i.2]
    · convert hS₃ using 1
      · simp only [FRI_code]
        rw [FRI_domain_succ_eq P i i.2]
        simp [FRI_degree]
      · rfl
