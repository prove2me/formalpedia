-- Prove2me | solution 1 for Formalism.L2.DIV.conjugation_invariant_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:47:24.600868+00:00
-- url     : https://prove2.me/submissions/c5ae2d69-9a6d-4192-8c23-1cbfa2b26003

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_idele_conjugation_involutive
import Theorems.Thm_Formalism_L2_DIV_mem_ker_norm_quotient_iff
import Theorems.Thm_Formalism_L2_DIV_fixed_field_is_base

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
namespace Formalism.L2.DIV
theorem _root_.solution : ConjInv := by
  intro F E _ _ _ _ _ L _ σ ξ hσ hξ
  ext1 x
  rw [MonoidHom.comp_apply, MonoidHom.inv_apply, eq_inv_iff_mul_eq_one, ← map_mul]
  have : conjId σ x * x ∈ (h90 σ).ker := by
    rw [mem_ker_norm_quotient_iff, map_mul, idele_conjugation_involutive σ hσ, mul_comm]
  rw [fixed_field_is_base F E σ hσ] at this
  exact hξ this
end Formalism.L2.DIV
