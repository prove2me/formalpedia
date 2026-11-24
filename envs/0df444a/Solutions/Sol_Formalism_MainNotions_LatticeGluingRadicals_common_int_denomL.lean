-- Prove2me | solution 1 for Formalism.MainNotions.LatticeGluingRadicals.common_int_denomL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:35.679824+00:00
-- url     : https://prove2.me/submissions/c9015679-6d2d-4f2f-996a-0cf5194e9ff5

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_JExistsNatSmulMemL
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.LatticeGluingRadicals
open NumberField
open scoped nonZeroDivisors
namespace Formalism.MainNotions.LatticeGluingRadicals
theorem _root_.solution {E : Type} [Field E] [NumberField E] {k : ℕ} (f : Fin k → E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = (m : E) * f i := by
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E :=
    IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  obtain ⟨⟨b, hb⟩, hf⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) f
  obtain ⟨m, hm, rfl⟩ := hb
  refine ⟨m, nonZeroDivisors.ne_zero hm, fun i => ?_⟩
  obtain ⟨r, hr⟩ := hf i
  refine ⟨r, ?_⟩
  rw [hr, Algebra.smul_def]
  simp
end Formalism.MainNotions.LatticeGluingRadicals
