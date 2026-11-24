-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.glob_glob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:21:46.235811+00:00
-- url     : https://prove2.me/submissions/d0face3a-cc17-4456-99d7-095ab992dccb

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
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
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.Comp
theorem _root_.solution {Λ : Submodule (𝓞 E) (n → E)} (h : IsLat Λ) (g k : GL n 𝒜) :
    globLat g (globLat k Λ) = globLat (g * k) Λ := by
  ext x
  show ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈ hat F (globLat k Λ) ↔
    (((g * k)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈ hat F Λ
  rw [mem_hat_glob h, mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul]
end Formalism.L2.GlobalTheoryTheory.Comp
