-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.mem_hat_map_glob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:43.018985+00:00
-- url     : https://prove2.me/submissions/05b7a652-e901-4a3d-8684-cf0f9b82981d

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_MemHatMapGlob
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_mem_hat_map
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_mem_hat_glob


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
    {Λ : Submodule (𝓞 E) (n → E)} (hΛ : IsLat Λ) (g : GL n 𝒜) (v : m → 𝒜) :
    v ∈ hat F (mapQ Q (globLat g Λ)) ↔
      (((conjQ Q Q' h1 h2 g)⁻¹ : GL m 𝒜) : Matrix m m 𝒜) *ᵥ v ∈ hat F (mapQ Q Λ) := by
  rw [mem_hat_map Q Q' h1 h2, mem_hat_glob hΛ, mem_hat_map Q Q' h1 h2]
  have e : Q'.map ιA * Q.map ιA = (1 : Matrix n n 𝒜) := map_mul_map Q' Q h2
  have : (Q'.map ιA) *ᵥ ((((conjQ Q Q' h1 h2 g)⁻¹ : GL m 𝒜) : Matrix m m 𝒜) *ᵥ v) =
      ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ ((Q'.map ιA) *ᵥ v) := by
    show (Q'.map ιA) *ᵥ ((Q.map ιA * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * Q'.map ιA) *ᵥ v) = _
    rw [mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e, Matrix.one_mul]
  rw [this]
end Formalism.L2.GlobalTheoryTheory.Comp
