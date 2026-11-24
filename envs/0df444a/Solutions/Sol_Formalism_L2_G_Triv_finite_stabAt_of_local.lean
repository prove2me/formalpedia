-- Prove2me | solution 1 for Formalism.L2.G.Triv.finite_stabAt_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:23:43.956016+00:00
-- url     : https://prove2.me/submissions/2861a31d-4111-466b-acc3-0b7ad06cdacc

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal
import Theorems.Thm_Formalism_L2_G_Triv_exists_den
import Theorems.Thm_Formalism_L2_G_Triv_den_upper
import Theorems.Thm_Formalism_L2_G_Triv_den_lower
import Theorems.Thm_Formalism_L2_G_Triv_loc_upper
import Theorems.Thm_Formalism_L2_G_Triv_loc_lower
import Theorems.Thm_Formalism_L2_G_Triv_levelafC_int
import Theorems.Thm_Formalism_UG_P_adelstab_core
import Theorems.Thm_Formalism_UG_P_afsplit_prV_inclE
import Theorems.Thm_Formalism_UG_P_afsplit_prV_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.L2.G.Triv
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E)
    (hτ : ∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (σ : E →+* E) J) (hdet : IsUnit J.det) (hdef : IsTotDef σ J)
    (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (U : Subgroup (GL n 𝒜))
    (hU : ∀ x ∈ U, ∀ v : HeightOneSpectrum (𝓞 F),
      bc (prV (E := E) v) x ∈ stabGL (latS (F := F) (v.adicCompletion F) (SV E v) Λ))
    (g : UPts σ J 𝔸) :
    Finite (stabAt ((ratPts σ J 𝔸).subgroupOf (UPts σ J 𝔸)) (U.subgroupOf (UPts σ J 𝔸)) g) := by
  obtain ⟨m₁, hm₁, h₁⟩ := den_lower Λ hspan
  obtain ⟨m₂, hm₂, h₂⟩ := den_upper Λ hfin
  obtain ⟨d, hd, h₃⟩ := exists_den (F := F) (E := E)
  refine adelstab_core σ J hτ hH hdet hdef (latLoc F Λ) U ?_ (m₁ : 𝓞 F) ((d * m₂ : ℤ) : 𝓞 F) (Int.cast_ne_zero.2 hm₁)
    (Int.cast_ne_zero.2 (mul_ne_zero hd hm₂)) ?_ ?_ g
  · intro x hx y
    have key : ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (((x : Matrix n n 𝒜) *ᵥ y) i)) =
        ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ
          fun i => prV (E := E) v (y i) := by
      intro v
      ext i
      exact RingHom.map_mulVec (prV (E := E) v) (x : Matrix n n 𝒜) y i
    constructor
    · intro hy v
      rw [key v]
      exact (hU x hx v _).1 (hy v)
    · intro hy v
      have := hy v
      rw [key v] at this
      exact (hU x hx v _).2 this
  · intro w hw v
    have : (fun i => prV (E := E) v (levelafC E (m₁ : 𝓞 F) * w i)) =
        fun i => inclE (F := F) (v.adicCompletion F) (m₁ : E) * prV (E := E) v (w i) := by
      ext i
      rw [levelafC_int, map_mul, afsplit_prV_inclE]
    rw [this]
    exact loc_lower Λ m₁ h₁ v _ fun i => afsplit_prV_int v _ (hw i)
  · intro w hw i
    rw [levelafC_int, Int.cast_mul, map_mul, mul_assoc]
    refine h₃ _ fun v => ?_
    rw [map_mul, afsplit_prV_inclE]
    exact loc_upper Λ m₂ h₂ v _ (hw v) i
end Formalism.L2.G.Triv
