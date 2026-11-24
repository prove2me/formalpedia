-- Prove2me | solution 1 for Formalism.L2.DIV.adele_conjugation_involutive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:44:13.491962+00:00
-- url     : https://prove2.me/submissions/0190eeb2-c8ba-4313-961b-d842f8431d98

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_conjugation_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.L2.DIV
theorem _root_.solution (σ : E →ₐ[F] E) (h : ∀ e, σ (σ e) = e) (z : AfE F E) :
    sigR σ 𝔸 (sigR σ 𝔸 z) = z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp only [map_zero]
  · intro e a
    rw [conjugation_tmul, conjugation_tmul, h]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
end Formalism.L2.DIV
