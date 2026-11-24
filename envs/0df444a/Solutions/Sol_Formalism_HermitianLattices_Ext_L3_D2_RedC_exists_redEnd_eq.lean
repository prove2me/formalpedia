-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.RedC.exists_redEnd_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:11:34.153484+00:00
-- url     : https://prove2.me/submissions/f9ad93c2-5d1c-4a64-82ce-09f581e84531

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Lemmata_GeneralBFactLeftRest_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemLocFOfSmulMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_RedC_redEnd_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_RedC_exists_lift
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_congrP_algebraMap_iff_sub_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_equiv_of_mem_endL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_congrP_algebraMap_iff_sub_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_isom_lift
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_exists_lift
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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k)
    (Y : Module.End (𝓞 K) (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀))))
    (hY : ∀ x y x' y' : ↥(locF 𝔭 A₀), Submodule.Quotient.mk x' = Y (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = Y (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) :
    ∃ (X : V ≃ₗ[K] V) (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k), redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 = Y := by
  obtain ⟨g, hg, hgY⟩ := exists_isom_lift hK hF hs hd hA₀ hA₀i h𝔭 hk Y hY
  have hgA : g ∈ glSub (locF 𝔭 A₀) := hg.2
  obtain ⟨D, hD⟩ := exists_lift hA₀ h𝔭 k Y
  have hle : extP K 𝔭 ^ (k - eA h (locF 𝔭 A₀) 𝔭) • locF 𝔭 A₀ ≤ extP K 𝔭 • locF 𝔭 A₀ :=
    Submodule.smul_mono_left (Ideal.pow_le_self (by omega))
  let E : V →ₗ[K] V := (g⁻¹ : V ≃ₗ[K] V).toLinearMap ∘ₗ D - LinearMap.id
  have hE : E ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀) := by
    intro x hx
    obtain ⟨hDx, h1⟩ := hD ⟨x, hx⟩
    have h2 := apply_mem_smul (inv_mem hgA) _ (hle (hgY ⟨x, hx⟩ ⟨D x, hDx⟩ h1))
    have h3 := neg_mem h2
    have e3 : E x = -(g⁻¹ (g x - D x)) := by
      simp [E]
    rw [e3]
    exact h3
  obtain ⟨Z, hZ, hZA⟩ := exists_equiv_of_mem_endL hA₀ h𝔭 hE
  have hXD : ∀ x, (g * Z) x = D x := fun x => by
    rw [LinearEquiv.mul_apply, hZ]
    simp [E]
  have hXA : g * Z ∈ glSub (locF 𝔭 A₀) := mul_mem hgA hZA
  have hmk : ∀ x : ↥(locF 𝔭 A₀), Submodule.Quotient.mk (⟨(g * Z) x, apply_mem hXA x.2⟩ : ↥(locF 𝔭 A₀)) =
      Y (Submodule.Quotient.mk x) := fun x => by
    obtain ⟨hDx, h1⟩ := hD x
    rw [← h1]
    congr 1
    exact Subtype.ext (hXD x)
  refine ⟨g * Z, ⟨hXA, fun x hx y hy => ?_⟩, ?_⟩
  · exact (congrP_algebraMap_iff_sub_mem h𝔭).1 (hY ⟨x, hx⟩ ⟨y, hy⟩ _ _ (hmk ⟨x, hx⟩) (hmk ⟨y, hy⟩))
  · refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    rw [redEnd_mk]
    exact hmk x
end Formalism.HermitianLattices.Ext.L3.D2.RedC
