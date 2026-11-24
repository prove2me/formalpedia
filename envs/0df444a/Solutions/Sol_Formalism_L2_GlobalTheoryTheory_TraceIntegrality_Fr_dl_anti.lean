-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.dl_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:51:11.331801+00:00
-- url     : https://prove2.me/submissions/eb75847d-fe0b-4501-a39e-66badd44727f

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL4_PFrCore
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_mem_dl


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
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.TraceIntegrality Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) {A B : Submodule (𝓞 E) (n → E)} (h : A ≤ B) :
    dl σ J B ≤ dl σ J A := fun y hy =>
  (mem_dl σ J A y).2 fun x hx => (mem_dl σ J B y).1 hy x (h hx)
end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
