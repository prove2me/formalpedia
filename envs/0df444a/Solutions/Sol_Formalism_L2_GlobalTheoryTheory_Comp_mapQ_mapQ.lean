-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.mapQ_mapQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:02:23.038197+00:00
-- url     : https://prove2.me/submissions/bb63cbb1-e2ce-492b-8c4d-0cd269c2b48c

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_MemHatMapGlob

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
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.Comp
theorem _root_.solution (Q : Matrix m n E) (Q' : Matrix n m E) (h : Q' * Q = 1) (Λ : Submodule (𝓞 E) (n → E)) :
    mapQ Q' (mapQ Q Λ) = Λ := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    show Q' *ᵥ (Q *ᵥ z) ∈ Λ
    rwa [mulVec_mulVec, h, one_mulVec]
  · intro hx
    exact ⟨Q *ᵥ x, ⟨x, hx, rfl⟩, by
      show Q' *ᵥ (Q *ᵥ x) = x
      rw [mulVec_mulVec, h, one_mulVec]⟩
end Formalism.L2.GlobalTheoryTheory.Comp
