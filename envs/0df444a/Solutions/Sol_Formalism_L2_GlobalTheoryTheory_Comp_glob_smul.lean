-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.glob_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:08:03.115802+00:00
-- url     : https://prove2.me/submissions/b428b3f3-1a02-4055-83ac-c2c16025a436

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_mono
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_isLat_glob
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_inv_glob
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_glob_inv
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_isLat_smul
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_smul_glob_le

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
theorem _root_.solution {A : Submodule (𝓞 E) (n → E)} (hA : IsLat A) {a : 𝓞 E} (ha : a ≠ 0) (g : GL n 𝒜) :
    globLat g (Ideal.span {a} • A) = Ideal.span {a} • globLat g A := by
  apply le_antisymm
  · have h1 := smul_glob_le (globLat g A) a g⁻¹
    rw [glob_glob_inv hA] at h1
    have h2 := glob_mono g h1
    rwa [glob_inv_glob (isLat_smul (isLat_glob hA g) ha)] at h2
  · exact smul_glob_le A a g
end Formalism.L2.GlobalTheoryTheory.Comp
