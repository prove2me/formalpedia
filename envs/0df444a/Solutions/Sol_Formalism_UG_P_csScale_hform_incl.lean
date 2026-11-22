-- Prove2me | solution 1 for Formalism.UG.P.csScale_hform_incl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:03.6824+00:00
-- url     : https://prove2.me/submissions/e8e356bf-680c-4676-984a-6d94440170ed

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsScale
import Theorems.Thm_Formalism_UG_P_csScale_sigR_incl

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
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (x y : n → E) :
    hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ιA) (fun i => ιA (x i)) (fun i => ιA (y i)) =
      ιA (hform (σ : E →+* E) J x y) := by
  simp only [hform, map_sum, map_mul, Matrix.map_apply, csScale_sigR_incl]
end Formalism.UG.P
