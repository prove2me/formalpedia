-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.mem_iff_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:16:49.664997+00:00
-- url     : https://prove2.me/submissions/bd881099-dccb-438d-9ab5-5af890e7a618

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutM
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_proj_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution {W₁ W₂ : Submodule K V} {N : AddSubgroup V} (hM : IsLatIn S h W₁ M)
    (hN : IsLatIn S h W₂ N) {x X : V} (hx : x ∈ M) (hX : X ∈ N) (hu : IsUnitIn S (h x x))
    {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hgx : g x = X)
    (hcut : ∀ v, v ∈ cutM h M x ↔ g v ∈ cutM h N X) : ∀ v, v ∈ M ↔ g v ∈ N := by
  have hgh : ∀ a b, h (g a) (g b) = h a b := fun a b => hg a b
  have hu' : IsUnitIn S (h X X) := by rw [← hgx, hgh]; exact hu
  intro v
  constructor
  · intro hv
    have hp := (hcut _).1 (proj_mem hM hx hu hv)
    have hc : h x v * (h x x)⁻¹ ∈ S := S.mul_mem (hM.int x hx v hv) hu.2.2
    have hgN := (mem_cutM.1 hp).1
    rw [map_sub, map_smul, hgx] at hgN
    have e := N.add_mem hgN (hN.smul_mem _ hc X hX)
    rwa [sub_add_cancel] at e
  · intro hv
    have hp := proj_mem hN hX hu' hv
    have hc : h X (g v) * (h X X)⁻¹ ∈ S := S.mul_mem (hN.int X hX _ hv) hu'.2.2
    have e : g v - (h X (g v) * (h X X)⁻¹) • X = g (v - (h x v * (h x x)⁻¹) • x) := by
      rw [map_sub, map_smul, ← hgx, hgh, hgh]
    rw [e] at hp
    have hm := (mem_cutM.1 ((hcut _).2 hp)).1
    have hc' : h x v * (h x x)⁻¹ ∈ S := by rwa [← hgx, hgh, hgh] at hc
    have e2 := M.add_mem hm (hM.smul_mem _ hc' x hx)
    rwa [sub_add_cancel] at e2
end Formalism.HermitianLattices.Ext.L3.U0
