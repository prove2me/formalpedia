-- Prove2me | solution 1 for Formalism.UG.P.csScale_glob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:30.75856+00:00
-- url     : https://prove2.me/submissions/147d04a9-dbe3-42b8-b98c-0fa481516ee2

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsScale
import Theorems.Thm_Formalism_UG_P_csScale_hform_incl
import Theorems.Thm_Formalism_UG_P_csScale_latS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.UG.P
open Formalism.UG
section Form
variable {A : Type} [CommRing A] {n : Type} [Fintype n]
end Form
section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
private theorem hform_mulVec_mulVec' {A ι : Type} [CommRing A] [Fintype ι] (τ : A →+* A)
    (K M : Matrix ι ι A) (u w : ι → A) :
    hform τ K (M *ᵥ u) (M *ᵥ w) = hform τ (cT τ M * K * M) u w := by
  have hf : ∀ (K' : Matrix ι ι A) (x y : ι → A), hform τ K' x y = (τ ∘ x) ⬝ᵥ (K' *ᵥ y) := by
    intro K' x y
    simp only [hform, Matrix.mulVec, _root_.dotProduct, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hτ : τ ∘ (M *ᵥ u) = M.map τ *ᵥ (τ ∘ u) := funext fun i => RingHom.map_mulVec τ M u i
  rw [hf, hf, hτ, ← Matrix.vecMul_transpose (M.map τ) (τ ∘ u), ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, cT]
end Main
end Formalism.UG.P
end
end

set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ)
    (hm : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((m : E) * hform (σ : E →+* E) J x y))
    (g : GL n 𝒜) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) {x y : n → E}
    (hx : x ∈ CS.globLat g Λ) (hy : y ∈ CS.globLat g Λ) :
    ιA ((m : E) * hform (σ : E →+* E) J x y) ∈ 𝒮 := by
  have hg0 : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix n n 𝒜) * J.map ιA *
      (g : Matrix n n 𝒜) = J.map ιA := hg
  have hback : ∀ v : n → 𝒜, (g : Matrix n n 𝒜) *ᵥ (((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hu : ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := hx
  have hw : ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (y i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := hy
  rw [map_mul, ← csScale_hform_incl, ← hback (fun i => ιA (x i)), ← hback (fun i => ιA (y i)),
    hform_mulVec_mulVec', hg0]
  exact csScale_latS σ J Λ m hm hu hw
end Formalism.UG.P
