-- Prove2me | solution 1 for Formalism.UG.P.adelstab_tr_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:39:20.410156+00:00
-- url     : https://prove2.me/submissions/5f5cf8e6-86b0-46b7-beb2-a26adf30a1dd

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
import Theorems.Thm_Formalism_UG_P_adelstabT_tmul
import Theorems.Thm_Formalism_UG_P_adelstabT_mem
import Theorems.Thm_Formalism_UG_P_adelstab_F_int

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
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.UG.P
theorem _root_.solution (e : E) (he : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e ∈ 𝒮) (b : 𝓞 E) :
    Algebra.trace F E (e * algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 F) F).range := by
  apply adelstab_F_int
  have h1 : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (e * algebraMap (𝓞 E) E b) ∈ 𝒮 := by
    rw [map_mul]; exact mul_mem he (adelstab_incl_int b)
  have := adelstabT_mem h1
  simpa [inclE, adelstabT_tmul] using this
end Formalism.UG.P
