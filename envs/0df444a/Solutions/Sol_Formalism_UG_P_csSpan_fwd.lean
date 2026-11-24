-- Prove2me | solution 1 for Formalism.UG.P.csSpan_fwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:05.649457+00:00
-- url     : https://prove2.me/submissions/74086f88-9b60-49bf-bf7a-e27842648b2c

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan

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
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) (g : GL n 𝒜) (u : n → 𝒜)
    (hu : u ∈ Submodule.span 𝒮 ((fun x : n → E => fun i => ι (x i)) ''
      (Formalism.UG.CS.globLat g Λ : Set (n → E)))) :
    ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by
  let Φ : (n → 𝒜) →ₗ[𝒮] (n → 𝒜) :=
    (Matrix.mulVecLin ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜)).restrictScalars 𝒮
  have hle : Submodule.span 𝒮 ((fun x : n → E => fun i => ι (x i)) ''
      (Formalism.UG.CS.globLat g Λ : Set (n → E))) ≤
      (latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ).comap Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  exact hle hu
end Formalism.UG.P
