-- Prove2me | solution 1 for Formalism.UG.P.stdform_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:42.273909+00:00
-- url     : https://prove2.me/submissions/2d411ec9-70e7-40ff-a154-cdbe663da159

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
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (e : E) : σ (σ e) = e := by
  apply τ.injective
  rw [stdform_conj σ τ hσ (σ e), stdform_conj σ τ hσ e, Complex.conj_conj]
end Formalism.UG.P
