-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.glob_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:08:04.090431+00:00
-- url     : https://prove2.me/submissions/fb86c556-0a8c-4382-bbc3-75c046c512c1

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_mono
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_isLat_glob
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_inv_glob
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_glob_inv
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_isLat_sup

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
theorem _root_.solution {A B : Submodule (𝓞 E) (n → E)} (hA : IsLat A) (hB : IsLat B) (g : GL n 𝒜) :
    globLat g (A ⊔ B) = globLat g A ⊔ globLat g B := by
  apply le_antisymm
  · have h1 : A ⊔ B ≤ globLat g⁻¹ (globLat g A ⊔ globLat g B) := by
      refine sup_le ?_ ?_
      · conv_lhs => rw [← glob_glob_inv hA g]
        exact glob_mono _ le_sup_left
      · conv_lhs => rw [← glob_glob_inv hB g]
        exact glob_mono _ le_sup_right
    have h2 := glob_mono g h1
    rwa [glob_inv_glob (isLat_sup (isLat_glob hA g) (isLat_glob hB g))] at h2
  · exact sup_le (glob_mono g le_sup_left) (glob_mono g le_sup_right)
end Formalism.L2.GlobalTheoryTheory.Comp
