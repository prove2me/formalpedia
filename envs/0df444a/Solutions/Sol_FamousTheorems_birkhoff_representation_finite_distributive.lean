-- Prove2me | solution 1 for FamousTheorems.birkhoff_representation_finite_distributive
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:13:34.523078+00:00
-- url     : https://prove2.me/submissions/594c3e44-ef3a-4d77-8f81-21e068cc4862

import Mathlib

theorem solution {α : Type*} [DistribLattice α] [Fintype α] [OrderBot α] :
    Nonempty (α ≃o LowerSet {a : α // SupIrred a}) :=
  ⟨by classical exact OrderIso.lowerSetSupIrred⟩
