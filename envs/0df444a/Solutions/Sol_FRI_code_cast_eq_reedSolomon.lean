-- Prove2me | solution 1 for FRI_code_cast_eq_reedSolomon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:41:43.245571+00:00
-- url     : https://prove2.me/submissions/35e4fd5f-047b-436e-9696-8eff8abf1e66

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (i : ℕ) (h : i < P.num_foldings) :
    FRI_code_cast P i h =
      reedSolomon (pow_domain (FRI_domain P i) (P.m ⟨i, h⟩)) (FRI_degree P (i + 1)) := by
  apply Submodule.ext
  intro f
  simp only [FRI_code_cast]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨fun x ↦ g.eval x, ⟨g, hg, rfl⟩, rfl⟩
