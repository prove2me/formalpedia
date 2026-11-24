-- Prove2me | solution 1 for Formalism.L2.DIV.hilbert90_finite_ideles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:23:43.090952+00:00
-- url     : https://prove2.me/submissions/ba08512c-8fdd-4f93-9758-c76fe3beff16

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_adele_conjugation_involutive
import Theorems.Thm_Formalism_L2_DIV_unitary_one_mem_range_norm_quotient

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
theorem _root_.solution : Hilbert90FiniteIdeles := by
  intro F E _ _ _ _ _ σ hσ
  apply le_antisymm
  · intro y hy
    exact unitary_one_mem_range_norm_quotient σ hσ y hy
  · rintro _ ⟨x, rfl⟩
    have hcc : conjId σ (conjId σ x) = x := Units.ext (adele_conjugation_involutive σ hσ.2.1 _)
    show h90 σ x * conjId σ (h90 σ x) = 1
    have h1 : h90 σ x = x / conjId σ x := rfl
    rw [h1, map_div, hcc, div_mul_div_cancel, div_self']
end Formalism.L2.DIV
