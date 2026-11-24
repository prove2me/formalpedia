-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:22:49.7506+00:00
-- url     : https://prove2.me/submissions/8eed169e-e52c-4f4e-b020-57e3d4d38f3c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_mem_orth
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_orth_symm
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_mem_iff_split
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Submodule K V} {S : Subring K} {M M₁ M₂ : AddSubgroup V}
namespace Formalism.L2.SG.Pf.LatDictZ.Z3
theorem _root_.solution (hs : h.IsSymm) (hc : IsCompl P (orth h P))
    (hsp₁ : Splits h P M₁) (hsp₂ : Splits h P M₂) (hag : ∀ w ∈ P, w ∈ M₁ ↔ w ∈ M₂)
    (g' : orth h P ≃ₗ[K] orth h P) (hg'i : ∀ x y : orth h P, h (g' x) (g' y) = h x y)
    (hg'M : ∀ x : orth h P, (x : V) ∈ M₁ ↔ (g' x : V) ∈ M₂) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ w ∈ P, g w = w) ∧ (∀ x : orth h P, g x = g' x) ∧
      ∀ x, x ∈ M₁ ↔ g x ∈ M₂ := by
  set e := Submodule.prodEquivOfIsCompl P (orth h P) hc with he
  let g : V ≃ₗ[K] V := e.symm.trans (((LinearEquiv.refl K P).prodCongr g').trans e)
  have hgs : ∀ x, e.symm (g x) = ((e.symm x).1, g' (e.symm x).2) := by
    intro x
    simp [g, LinearEquiv.prodCongr_apply]
  have hgx : ∀ x, g x = ((e.symm x).1 : V) + (g' (e.symm x).2 : V) := by
    intro x
    have := e.apply_symm_apply (g x)
    rw [hgs x, he, Submodule.coe_prodEquivOfIsCompl'] at this
    exact this.symm
  have hx : ∀ x, x = ((e.symm x).1 : V) + ((e.symm x).2 : V) := by
    intro x
    have := e.apply_symm_apply x
    rw [he, Submodule.coe_prodEquivOfIsCompl'] at this
    exact this.symm
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro x y
    change h (g x) (g y) = h x y
    rw [hgx x, hgx y]
    conv_rhs => rw [hx x, hx y]
    have z1 : ∀ (c : P) (d : orth h P), h (c : V) (d : V) = 0 := fun c d => mem_orth.mp d.2 c c.2
    have z2 : ∀ (c : P) (d : orth h P), h (d : V) (c : V) = 0 := fun c d => orth_symm hs c.2 d.2
    simp only [map_add, LinearMap.add_apply, z1, z2, hg'i, add_zero, zero_add]
  · intro w hw
    have e1 : e.symm w = (⟨w, hw⟩, 0) := Submodule.prodEquivOfIsCompl_symm_apply_left P (orth h P) hc ⟨w, hw⟩
    rw [hgx w, e1]
    simp
  · intro x
    have e1 : e.symm x = (0, x) := Submodule.prodEquivOfIsCompl_symm_apply_right P (orth h P) hc x
    rw [hgx x, e1]
    simp
  · intro x
    rw [mem_iff_split hc hsp₁ x, mem_iff_split hc hsp₂ (g x), hgs x]
    exact and_congr (hag _ (e.symm x).1.2) (hg'M _)
end Formalism.L2.SG.Pf.LatDictZ.Z3
