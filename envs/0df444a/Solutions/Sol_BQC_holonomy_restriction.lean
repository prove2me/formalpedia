-- Prove2me | solution 1 for BQC.holonomy_restriction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:05:03.763995+00:00
-- url     : https://prove2.me/submissions/e8ad7401-ae88-4173-bb86-e00655dd83be

import Mathlib
import Definitions.Def_BQC_alg
import Definitions.Def_BQC_tor
open BQC

theorem solution {d : Nat} {Cry Ph : Type*} [Group Cry] [Group Ph] [Fintype Ph]
    (W : CryWorld d Cry Ph) {H : Type} [Group H] [Fintype H] (j : H →* Ph)
    (hinj : ∀ x y : H, j x = j y → x = y) :
    ∃ T : Subgroup Cry, ∀ p : Cry, p ∈ T ↔ ∃ h : H, W.proj p = j h := by
  refine ⟨(j.range).comap W.proj, fun p => ?_⟩
  simp only [Subgroup.mem_comap, MonoidHom.mem_range]
  constructor
  · rintro ⟨h, hh⟩; exact ⟨h, hh.symm⟩
  · rintro ⟨h, hh⟩; exact ⟨h, hh.symm⟩
