-- Prove2me | solution 1 for BookProof.KatoRellich.symmetricOn_add
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T02:15:06.568037+00:00
-- url     : https://prove2.me/submissions/03b81162-bc7e-4366-b8a6-790ffe1a03e1

import Definitions.Def_ChapterFarisLavineCore

open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

-- Direct proof from the registered statement using Mathlib.
theorem solution {H B : D →ₗ[ℂ] F} (hH : SymmetricOn D H) (hB : SymmetricOn D B) :
    SymmetricOn D (H + B) := by
  intro x y
  simp only [LinearMap.add_apply, inner_add_left, inner_add_right]
  rw [hH x y, hB x y]

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
