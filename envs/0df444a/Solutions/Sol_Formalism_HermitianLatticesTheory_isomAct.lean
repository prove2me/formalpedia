-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.isomAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:30.810836+00:00
-- url     : https://prove2.me/submissions/368ba3e3-e017-4090-bb62-ec883ca4a1b4

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_gmap
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_smul
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_gmap_symm
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_lattice
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_locS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : IsomAct := by
  intro R K V _ _ _ _ _ _ _ _ h g hg L
  have iso : ∀ x y, h (g x) (g y) = h x y := hg
  have hdual : dual h (gmap g L) = gmap g (dual h L) := by
    ext x
    rw [isomAct_mem_gmap, isomAct_mem_dual, isomAct_mem_dual]
    constructor
    · intro H z hz
      have hz' : g z ∈ gmap g L := by
        rw [isomAct_mem_gmap]
        simpa using hz
      have e := H (g z) hz'
      rw [← iso z (g.symm x)]
      simpa using e
    · intro H y hy
      rw [isomAct_mem_gmap] at hy
      have e := H _ hy
      rw [← iso (g.symm y) (g.symm x)] at e
      simpa using e
  have hsat : ∀ S : Submonoid R, locS S (gmap g L) = gmap g (locS S L) := by
    intro S
    ext x
    simp only [isomAct_mem_gmap, isomAct_mem_locS, isomAct_smul]
  have hint_r : IsIntegralLat h (gmap g L) ↔ IsIntegralLat h L := by
    unfold IsIntegralLat
    constructor
    · intro H x hx y hy
      have hx' : g x ∈ gmap g L := by
        rw [isomAct_mem_gmap]
        simpa using hx
      have hy' : g y ∈ gmap g L := by
        rw [isomAct_mem_gmap]
        simpa using hy
      rw [← iso x y]
      exact H _ hx' _ hy'
    · intro H x hx y hy
      rw [isomAct_mem_gmap] at hx hy
      have e := H _ hx _ hy
      rw [← iso (g.symm x) (g.symm y)] at e
      simpa using e
  have hunim : IsUnimodular h (gmap g L) ↔ IsUnimodular h L := by
    unfold IsUnimodular
    rw [hdual]
    constructor
    · intro H
      have e := congrArg (gmap (R := R) g.symm) H
      simp only [isomAct_gmap_symm] at e
      exact e
    · intro H
      rw [H]
  have hlat : Submodule.IsLattice K (gmap g L) ↔ Submodule.IsLattice K L := by
    constructor
    · intro H
      have e := isomAct_lattice g.symm (gmap g L) H
      rwa [isomAct_gmap_symm] at e
    · intro H
      exact isomAct_lattice g L H
  refine ⟨hdual, ?_, hint_r, hunim, hlat⟩
  intro p
  unfold loc
  exact hsat _
end Formalism.HermitianLatticesTheory
