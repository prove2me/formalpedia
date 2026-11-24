-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.glob_inv_glob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:42:36.252801+00:00
-- url     : https://prove2.me/submissions/517cea90-ec05-40ad-ac07-7409db43b471

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_one
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_glob

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
theorem _root_.solution {Λ : Submodule (𝓞 E) (n → E)} (h : IsLat Λ) (g : GL n 𝒜) :
    globLat g (globLat g⁻¹ Λ) = Λ := by
  rw [glob_glob h, mul_inv_cancel, glob_one h]
end Formalism.L2.GlobalTheoryTheory.Comp
