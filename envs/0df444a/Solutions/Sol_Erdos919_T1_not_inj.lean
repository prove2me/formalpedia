-- Prove2me | solution 1 for Erdos919.T1_not_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:34:51.735453+00:00
-- url     : https://prove2.me/submissions/dd0366a9-3761-4c3e-89d3-85c7538a8fb5

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_mk_T1

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution (d : T1.{u} → ULift.{u} ℕ) : ∃ t₁ t₂, t₁ ≠ t₂ ∧ d t₁ = d t₂ := by
  by_contra h
  push Not at h
  have hinj : Function.Injective d := fun a b hab => by
    by_contra hne
    exact h a b hne hab
  have := mk_le_of_injective hinj
  rw [mk_T1, mk_uLift, mk_nat, lift_aleph0] at this
  exact absurd this (not_le.2 aleph0_lt_aleph_one)
end Erdos919
