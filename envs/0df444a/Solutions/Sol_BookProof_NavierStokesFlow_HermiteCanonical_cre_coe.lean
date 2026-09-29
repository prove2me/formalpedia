-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteCanonical.cre_coe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:26:28.687192+00:00
-- url     : https://prove2.me/submissions/3fcbe171-cafe-46c0-88e1-c90aa87f19fe

import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
noncomputable section

theorem solution (x : lpFiniteModes ℕ) (n : ℕ) :
    (((cre x : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n =
      (Real.sqrt n : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) (n - 1) := by
  rfl
