-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF.same_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:54:28.520297+00:00
-- url     : https://prove2.me/submissions/0cd4f534-86dc-4b17-9916-b4b55ece2222

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjMemAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AutSubApplyMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_autSub_apply_mem
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_gmap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_IsStep_change
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_extOf_res
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_res_mem_isom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_isom_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    {g₁ g₂ : V ≃ₗ[K] V} (hg₁ : g₁ ∈ Formalism.HermitianLatticesTheory.isom h) (hg₂ : g₂ ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx₁ : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L)) (hx₂ : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₂ (locF 𝔭 L))
    {J : ℕ} (hJ : 4 * vF 𝔭 n + eA h (locF 𝔭 L) 𝔭 + 1 ≤ J) {y : V}
    (h1 : y ∈ tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J (g₁.symm S.x₀))
    (h2 : y ∈ tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J (g₂.symm S.x₀)) :
    ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') (Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L)) =
      Formalism.HermitianLatticesTheory.gmap g₂ (locF 𝔭 L) := by
  have hx₁' : g₁.symm S.x₀ ∈ locF 𝔭 L := (Formalism.HermitianLatticesTheory.isomAct_mem_gmap g₁ (locF 𝔭 L) S.x₀).1 hx₁
  have hx₂' : g₂.symm S.x₀ ∈ locF 𝔭 L := (Formalism.HermitianLatticesTheory.isomAct_mem_gmap g₂ (locF 𝔭 L) S.x₀).1 hx₂
  obtain ⟨u₁, hu₁, hy₁⟩ := h1
  obtain ⟨u₂, hu₂, hy₂⟩ := h2
  have ha : u₁ (g₁.symm S.x₀) ∈ locF 𝔭 L := autSub_apply_mem hu₁ hx₁'
  have hb : u₂ (g₂.symm S.x₀) ∈ locF 𝔭 L := autSub_apply_mem hu₂ hx₂'
  have hna : h (u₁ (g₁.symm S.x₀)) (u₁ (g₁.symm S.x₀)) = algebraMap F K (n : F) := by
    rw [SplitBAux.isom_apply hu₁.1, SplitBAux.isom_apply (SplitBAux.symm_mem_isom hg₁), hx]
  have hnb : h (u₂ (g₂.symm S.x₀)) (u₂ (g₂.symm S.x₀)) = algebraMap F K (n : F) := by
    rw [SplitBAux.isom_apply hu₂.1, SplitBAux.isom_apply (SplitBAux.symm_mem_isom hg₂), hx]
  have hxy : u₂ (g₂.symm S.x₀) - u₁ (g₁.symm S.x₀) ∈
      ((extP K 𝔭) ^ J • (locF 𝔭 L) : Submodule (𝓞 K) V) := by
    have e : u₂ (g₂.symm S.x₀) - u₁ (g₁.symm S.x₀) =
        (y - u₁ (g₁.symm S.x₀)) - (y - u₂ (g₂.symm S.x₀)) := by abel
    rw [e]
    exact sub_mem hy₁ hy₂
  obtain ⟨w, hw, -, hwab⟩ := exists_isom_congr hK hF hs hd hL hLi h𝔭 hn ha hb hna hnb hJ hxy
  set G : V ≃ₗ[K] V := g₂ * u₂⁻¹ * w * u₁ * g₁⁻¹ with hGdef
  have hG : G ∈ Formalism.HermitianLatticesTheory.isom h :=
    mul_mem (mul_mem (mul_mem (mul_mem hg₂ (inv_mem hu₂.1)) hw.1) hu₁.1) (inv_mem hg₁)
  have hGx : G S.x₀ = S.x₀ := by
    change g₂ (u₂.symm (w (u₁ (g₁.symm S.x₀)))) = S.x₀
    rw [hwab, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  refine ⟨SplitBAux.res S G hG hGx, SplitBAux.res_mem_isom S G hG hGx, ?_⟩
  rw [extOf_res, ← autSub_gmap_mul]
  have e : G * g₁ = g₂ * u₂⁻¹ * w * u₁ := by
    rw [hGdef, inv_mul_cancel_right]
  rw [e, autSub_gmap_mul, hu₁.2, autSub_gmap_mul, hw.2, autSub_gmap_mul, (inv_mem hu₂).2]
end Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF
