-- Prove2me | solution 1 for FamousTheorems.character_orthonormality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:08:57.217889+00:00
-- url     : https://prove2.me/submissions/3a0888d3-aa23-4aef-859f-5244ae7f1664

import Mathlib

open scoped Classical

theorem solution {k G : Type*} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [Invertible (Nat.card G : k)]
    (V W : FDRep k G) [CategoryTheory.Simple V] [CategoryTheory.Simple W] :
    (Nat.card G : k)⁻¹ * ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (CategoryTheory.Iso V W) then 1 else 0 :=
  FDRep.char_orthonormal V W
