-- Prove2me | solution 1 for FamousTheorems.bicategory_coherence_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:53:00.078381+00:00
-- url     : https://prove2.me/submissions/c696e44d-e07c-4b3e-ac97-00e517b3d37f

import Mathlib

theorem solution {B : Type*} [Quiver B] (a b : CategoryTheory.FreeBicategory B) : Quiver.IsThin (a ⟶ b) :=
  CategoryTheory.FreeBicategory.locally_thin
