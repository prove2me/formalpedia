-- Prove2me | solution 1 for Formalism.L2.DIV.hilbert90_quadratic_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:47:35.730843+00:00
-- url     : https://prove2.me/submissions/1b3f9849-1124-4908-b243-924435e2c365

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_exists_conjugation_negated

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
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace Formalism.L2.DIV
theorem _root_.solution (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (d : E) (hd : σ d * d = 1) :
    ∃ x : E, x ≠ 0 ∧ x = d * σ x := by
  by_cases h : 1 + d = 0
  · obtain ⟨θ, h0, hθ⟩ := exists_conjugation_negated σ hσ
    refine ⟨θ, h0, ?_⟩
    have : d = -1 := by linear_combination h
    rw [hθ, this]; ring
  · refine ⟨1 + d, h, ?_⟩
    rw [map_add, map_one]
    linear_combination -hd
end Formalism.L2.DIV
