-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.fockDom_dense
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:44:08.702536+00:00
-- url     : https://prove2.me/submissions/f7fe56e2-2ea1-4f74-88bb-aae4dd97adac

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

variable {M : Type*}

theorem solution [DecidableEq M] : Dense ((FockDom M : Submodule ℂ (FockL2 M)) : Set (FockL2 M)) :=
  lpFiniteModes_dense


#print axioms solution
