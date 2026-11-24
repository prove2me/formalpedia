-- Prove2me | solution 1 for Formalism.L2.DIV.conjugation_fixed_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:08:17.675822+00:00
-- url     : https://prove2.me/submissions/c7216e01-883f-4646-b3ad-fe2e44d7e788

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_add_conjugation_mem_range

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
theorem _root_.solution [CharZero F] (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (R : Type) [CommRing R] [Algebra F R]
    (z : E ⊗[F] R) (hz : sigR σ R z = z) :
    z ∈ (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R).range := by
  have h := add_conjugation_mem_range σ hσ R z
  rw [hz] at h
  have h2 : z = (2⁻¹ : F) • (z + z) := by
    rw [← two_smul F z, smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
  rw [h2]; exact Subalgebra.smul_mem _ h _
end Formalism.L2.DIV
