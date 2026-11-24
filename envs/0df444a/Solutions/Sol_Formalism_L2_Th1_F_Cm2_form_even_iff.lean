-- Prove2me | solution 1 for Formalism.L2.Th1.F.Cm2.form_even_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:24:02.803087+00:00
-- url     : https://prove2.me/submissions/861c0808-1966-4be3-aca9-c85260897d1e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_FormEvenIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Cm2
open Cm1
namespace Formalism.L2.Th1.F.Cm2
theorem _root_.solution (a b c m n : ℤ) (ha : Odd a) (hb : Odd b) (hc : Even c) :
    Even (cmForm a b c m n) ↔ (Even m ∨ Odd n) := by
  have ha' : ¬ Even a := Int.not_even_iff_odd.mpr ha
  have hb' : ¬ Even b := Int.not_even_iff_odd.mpr hb
  rw [← Int.not_even_iff_odd]
  first
    | simp only [cmForm, Int.even_add, Int.even_mul, Int.even_pow' two_ne_zero]
    | simp only [cmForm, Int.even_add, Int.even_mul, Int.even_pow, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, and_true]
  tauto
end Formalism.L2.Th1.F.Cm2
