-- Prove2me | solution 1 for Formalism.UG.P.stdform_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:51.191648+00:00
-- url     : https://prove2.me/submissions/df2933a0-a8e3-4fcb-bb36-3df2b25e1b2f

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform

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
namespace Formalism.UG.P
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (ι : F →+* ℝ) :
    ∃ τ : E →+* ℂ, τ.comp (algebraMap F E) = (algebraMap ℝ ℂ).comp ι := by
  letI : Algebra F ℂ := ((algebraMap ℝ ℂ).comp ι).toAlgebra
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  refine ⟨(IsAlgClosed.lift : E →ₐ[F] ℂ).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : E →ₐ[F] ℂ).commutes x
end Formalism.UG.P
