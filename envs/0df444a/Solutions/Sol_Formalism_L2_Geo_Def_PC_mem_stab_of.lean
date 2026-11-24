-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PC.mem_stab_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:08:18.048298+00:00
-- url     : https://prove2.me/submissions/002aeb77-c860-4931-b513-7cc4b092c57c

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassD
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassE

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
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
omit [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.Geo.Def.PC
theorem _root_.solution {A R : Type} [CommRing A] [CommRing R] [Algebra R A] (Λ : Submodule R (n → A)) (g : GL n A)
    (h1 : ∀ x ∈ Λ, (g : Matrix n n A) *ᵥ x ∈ Λ)
    (h2 : ∀ x ∈ Λ, ((g⁻¹ : GL n A) : Matrix n n A) *ᵥ x ∈ Λ) : g ∈ stabGL Λ := by
  unfold stabGL
  refine fun x => ⟨h1 x, fun hx => ?_⟩
  have h3 := h2 _ hx
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h3
end Formalism.L2.Geo.Def.PC
