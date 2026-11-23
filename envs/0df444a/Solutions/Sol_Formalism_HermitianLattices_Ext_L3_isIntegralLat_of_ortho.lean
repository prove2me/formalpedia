-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.isIntegralLat_of_ortho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:55.0708+00:00
-- url     : https://prove2.me/submissions/a60b6f03-63a2-438e-a005-14bedf49a39f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StandardSymmetricSums_form_sum
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StandardSymmetricSums_star_int
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StandardSymmetricSums_mem_lat_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open StandardSymmetricSums
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : Formalism.HermitianLatticesTheory.IsIntegralLat h L := by
  obtain ⟨e, hli, hsp, rfl, he⟩ := hL
  intro x hx y hy
  obtain ⟨c, rfl⟩ := (mem_lat_iff x).1 hx
  obtain ⟨d, rfl⟩ := (mem_lat_iff y).1 hy
  rw [form_sum he]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨t, ht⟩ := star_int (c i)
  rw [← ht, ← map_mul]
  exact Submodule.mem_one.2 ⟨_, rfl⟩
end Formalism.HermitianLattices.Ext.L3
