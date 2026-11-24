-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BrA.form_mem_locF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:11.589033+00:00
-- url     : https://prove2.me/submissions/f7d7bd36-44d5-4844-8d3b-a2b06ec74427

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_locF_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_form_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module IsDedekindDomain Function
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BrA
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {g : V ≃ₗ[K] V}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {x y : V} (hx : x ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))
    (hy : y ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) : h x y ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  obtain ⟨x', hx', ex⟩ := Submodule.mem_map.mp hx
  obtain ⟨y', hy', ey⟩ := Submodule.mem_map.mp hy
  have ex' : g x' = x := ex
  have ey' : g y' = y := ey
  obtain ⟨s, hs, hsx⟩ := (LocF.mem_locF_iff hp L x').mp hx'
  obtain ⟨t, ht, hty⟩ := (LocF.mem_locF_iff hp L y').mp hy'
  rw [← ex', ← ey', hg x' y', LocF.mem_locF_iff hp]
  refine ⟨s * t, fun hm => (hp.mem_or_mem hm).elim hs ht, ?_⟩
  have := hLi _ hsx _ hty
  rw [localizedQuotients.form_smul hF] at this
  rwa [Algebra.smul_def]
end Formalism.HermitianLattices.Ext.L3.BrA
