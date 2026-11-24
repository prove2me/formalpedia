-- Prove2me | solution 1 for Formalism.L2.DIV.exists_conjugation_negated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:26:45.660369+00:00
-- url     : https://prove2.me/submissions/347331f0-6360-4dfd-b8fd-95ffafad139d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP

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
theorem _root_.solution (σ : E →ₐ[F] E) (hσ : IsConjOf σ) : ∃ θ : E, θ ≠ 0 ∧ σ θ = -θ := by
  have : ∃ e, σ e ≠ e := by
    by_contra h
    exact hσ.1 (AlgHom.ext fun e => by_contra fun he => h ⟨e, he⟩)
  obtain ⟨e, he⟩ := this
  exact ⟨e - σ e, sub_ne_zero.mpr (Ne.symm he), by rw [map_sub, hσ.2.1]; ring⟩
end Formalism.L2.DIV
