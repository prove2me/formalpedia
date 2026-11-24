-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.RedC.redEnd_cond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:23:07.593788+00:00
-- url     : https://prove2.me/submissions/7db2d622-7aff-4835-bba4-006f9b73118e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Lemmata_GeneralBFactLeftRest_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemLocFOfSmulMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_RedC_mk_eq_redEnd_iff
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_congrP_algebraMap_iff_sub_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_form_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_pow_zero_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_congrP_algebraMap_iff_sub_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.RedC
namespace Formalism.HermitianLattices.Ext.L3.D2.RedC
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {X : V ≃ₗ[K] V}
    (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k) (x y x' y' : ↥(locF 𝔭 A₀))
    (hx : Submodule.Quotient.mk x' = redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 (Submodule.Quotient.mk x))
    (hy : Submodule.Quotient.mk y' = redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 (Submodule.Quotient.mk y)) :
    CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V)) := by
  rw [congrP_algebraMap_iff_sub_mem h𝔭]
  rw [mk_eq_redEnd_iff] at hx hy
  have z : ∀ w ∈ locF 𝔭 A₀, w ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀ := fun w hw => by rwa [pow_zero_smul]
  have h1 := hX.2 x x.2 y y.2
  have h2 := form_mem_pK hF hA₀i h𝔭 hx (z _ y'.2)
  have h3 := form_mem_pK hF hA₀i h𝔭 (z _ (apply_mem hX.1 x.2)) hy
  rw [add_zero] at h2
  rw [zero_add] at h3
  have h4 := add_mem (add_mem h1 h2) h3
  have e : h (x' : V) (y' : V) - h (x : V) (y : V) =
      h (X x) (X y) - h (x : V) (y : V) + h ((x' : V) - X x) (y' : V) + h (X x) ((y' : V) - X y) := by
    simp only [map_sub, LinearMap.sub_apply]
    abel
  rw [e]
  exact h4
end Formalism.HermitianLattices.Ext.L3.D2.RedC
