-- Prove2me | solution 1 for Formalism.UG.P.adelstab_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:15:19.866807+00:00
-- url     : https://prove2.me/submissions/90f49aa4-8480-4b54-b359-a9b2cb100690

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
import Theorems.Thm_Formalism_UG_P_adelstab_stab
import Theorems.Thm_Formalism_UG_P_adelstab_span
import Theorems.Thm_Formalism_UG_P_adelstab_finite
import Theorems.Thm_Formalism_UG_P_adelstab_entries
import Theorems.Thm_Formalism_UG_P_UG_stabilizer_finite
import Theorems.Thm_Formalism_UG_P_levelaf_exists_denom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E)
    (hτ : ∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (σ : E →+* E) J) (hdet : IsUnit J.det) (hdef : IsTotDef σ J)
    (L : Submodule 𝒮 (n → 𝒜)) (K : Subgroup (GL n 𝒜)) (hK : K ≤ stabGL L) (c₁ c₂ : 𝓞 F)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hL₁ : ∀ v : n → 𝒜, (∀ i, v i ∈ 𝒮) → (fun i => levelafC E c₁ * v i) ∈ L)
    (hL₂ : ∀ v ∈ L, ∀ i, levelafC E c₂ * v i ∈ 𝒮)
    (g : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    Finite (stabAt ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf
      (UPts σ J (FiniteAdeleRing (𝓞 F) F))) (K.subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) g) := by
  classical
  set G : GL n 𝒜 := (g : GL n 𝒜)
  obtain ⟨d, hd, c, hc, hcg, hcgi⟩ := levelaf_exists_denom (E := E) G
  have hG := adelstab_entries G d c hc hcg
  have hGi := adelstab_entries G⁻¹ d c hc hcgi
  have hF : Finite (level (σ : E →+* E) J (adelstabLam F E G L)) :=
    UG_stabilizer_finite F E n σ J hτ hH hdet hdef _ (adelstab_finite G L c₂ d hc₂ hd hL₂ hG)
      (adelstab_span G L c₁ d hc₁ hd hL₁ hGi)
  have hrat : ∀ γ : stabAt ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf
      (UPts σ J (FiniteAdeleRing (𝓞 F) F))) (K.subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) g,
      ∃ γ₀ : GL n E, γ₀ ∈ UJ (σ : E →+* E) J ∧ bc ι γ₀ = (((γ : _) : _) : GL n 𝒜) := by
    intro γ
    have h1 := Subgroup.mem_subgroupOf.1 γ.1.2
    obtain ⟨γ₀, h2, h3⟩ := Subgroup.mem_map.1 h1
    exact ⟨γ₀, h2, h3⟩
  choose f hfU hfeq using hrat
  have hmem : ∀ γ, f γ ∈ level (σ : E →+* E) J (adelstabLam F E G L) := by
    intro γ
    refine Subgroup.mem_inf.2 ⟨hfU γ, adelstab_stab G L (f γ) (hK ?_)⟩
    have h1 := Subgroup.mem_subgroupOf.1 γ.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [hfeq γ]
    exact h1
  refine Finite.of_injective (fun γ => (⟨f γ, hmem γ⟩ : level (σ : E →+* E) J (adelstabLam F E G L))) ?_
  intro γ γ' h
  have h' : bc ι (f γ) = bc ι (f γ') := by
    have := congrArg (fun z : level (σ : E →+* E) J (adelstabLam F E G L) => bc ι (z : GL n E)) h
    simpa using this
  rw [hfeq, hfeq] at h'
  exact Subtype.ext (Subtype.ext (Subtype.ext h'))
end Formalism.UG.P
