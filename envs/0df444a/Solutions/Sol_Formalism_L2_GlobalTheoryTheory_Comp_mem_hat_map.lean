-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.mem_hat_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:12:16.672031+00:00
-- url     : https://prove2.me/submissions/b130a288-8957-4896-82d1-ebdf8c92e9e0

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_MemHatMapGlob
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_mapQ_mapQ
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_hat_map_le

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
theorem _root_.solution (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1) (h2 : Q' * Q = 1)
    (Λ : Submodule (𝓞 E) (n → E)) (v : m → 𝒜) : v ∈ hat F (mapQ Q Λ) ↔ (Q'.map ιA) *ᵥ v ∈ hat F Λ := by
  constructor
  · intro hv
    have := hat_map_le (F := F) Q' (mapQ Q Λ) v hv
    rwa [mapQ_mapQ Q Q' h2] at this
  · intro hv
    have := hat_map_le (F := F) Q Λ _ hv
    rwa [mulVec_mulVec, map_mul_map Q Q' h1, one_mulVec] at this
end Formalism.L2.GlobalTheoryTheory.Comp
