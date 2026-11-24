-- Prove2me | solution 1 for Formalism.UG.P.stdform_hform_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:41.52522+00:00
-- url     : https://prove2.me/submissions/955f4d7f-ab84-46f9-8662-94c1c06161de

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Theorems.Thm_Formalism_UG_P_stdform_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {n : Type} [Fintype n] [DecidableEq n] {F E : Type} [Field F] [Field E] [Algebra F E]
namespace Formalism.UG.P
theorem _root_.solution (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (J : Matrix n n E) (x : n → E) :
    τ (hform (σ : E →+* E) J x x) =
      ∑ i, ∑ j, starRingEnd ℂ (τ (x i)) * (J.map τ) i j * τ (x j) := by
  simp only [hform, map_sum, map_mul, Matrix.map_apply, AlgHom.coe_toRingHom, stdform_conj σ τ hσ]
end Formalism.UG.P
