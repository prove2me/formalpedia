-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.isLat_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:02:22.15592+00:00
-- url     : https://prove2.me/submissions/8c9ccc40-d2e4-450b-8c85-2e984b56ea8f

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat

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
theorem _root_.solution {A B : Submodule (𝓞 E) (n → E)} (hA : IsLat A) (hB : IsLat B) : IsLat (A ⊔ B) := by
  refine ⟨Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hA.1).sup (Module.Finite.iff_fg.1 hB.1)), ?_⟩
  rw [eq_top_iff, ← hA.2]
  exact Submodule.span_mono (fun x hx => (le_sup_left : A ≤ A ⊔ B) hx)
end Formalism.L2.GlobalTheoryTheory.Comp
