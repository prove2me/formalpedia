-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.bc_mem_UPts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:52:40.616259+00:00
-- url     : https://prove2.me/submissions/4dbd16d1-e811-46a2-ba24-010b106a5569

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL4_PFrCore
import Theorems.Thm_Formalism_UG_P_base_change_mem_holds
import Theorems.Thm_Formalism_UG_P_csDual_sig_incl


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
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (G : GL n E) (hG : G ∈ UJ (σ : E →+* E) J) :
    bc ιA G ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  have hc : (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)).comp (σ : E →+* E) =
      (sigR σ (FiniteAdeleRing (𝓞 F) F)).comp (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) :=
    RingHom.ext fun a => (csDual_sig_incl σ a).symm
  exact base_change_mem_holds _ _ n _ _ ιA hc J G hG
end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
