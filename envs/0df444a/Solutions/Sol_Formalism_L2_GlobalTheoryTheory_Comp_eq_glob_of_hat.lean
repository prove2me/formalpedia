-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.eq_glob_of_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:42:09.0834+00:00
-- url     : https://prove2.me/submissions/2b8a589c-391f-4070-a513-bb40f62ad497

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_one

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
theorem _root_.solution {Λ M : Submodule (𝓞 E) (n → E)} (hM : IsLat M) (g : GL n 𝒜)
    (h : ∀ u : n → 𝒜, u ∈ hat F M ↔ ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F Λ) : M = globLat g Λ := by
  rw [← glob_one (F := F) hM]
  ext x
  show (((1 : GL n 𝒜)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈ hat F M ↔
    ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈ hat F Λ
  rw [inv_one, Units.val_one, one_mulVec, h]
end Formalism.L2.GlobalTheoryTheory.Comp
