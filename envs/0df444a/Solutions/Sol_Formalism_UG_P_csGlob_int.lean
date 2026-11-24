-- Prove2me | solution 1 for Formalism.UG.P.csGlob_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:15:12.830705+00:00
-- url     : https://prove2.me/submissions/527fe12c-ca34-4d83-b89c-eb786a33c5dc

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlobApprox
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Theorems.Thm_Formalism_UG_P_csGlob_N_fg

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
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (e : E) (he : ι e ∈ 𝒮) : IsIntegral ℤ e := by
  have hne : csGlobN F E ≠ ⊥ := by
    intro h
    have h1 : (1 : E) ∈ csGlobN F E := by
      show ι 1 ∈ 𝒮
      rw [map_one]; exact one_mem _
    rw [h, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  have hI : IsIntegral (𝓞 F) e := isIntegral_of_smul_mem_submodule (csGlobN F E) hne csGlob_N_fg e
    (fun m hm => by
      show ι (e * m) ∈ 𝒮
      rw [map_mul]; exact mul_mem he hm)
  exact isIntegral_trans (R := ℤ) (A := 𝓞 F) e hI
end Formalism.UG.P
