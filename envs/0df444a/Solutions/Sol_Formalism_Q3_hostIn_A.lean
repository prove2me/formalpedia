-- Prove2me | solution 1 for Formalism.Q3.hostIn_A
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:23.775874+00:00
-- url     : https://prove2.me/submissions/5835c8b2-65fa-43cb-8873-9bb788ca8be8

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostInertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution (q : Fin 3 → ℕ) {E : Type} [Field E] [NumberField E] (α : Fin 3 → E)
    (hα : IsHost q α) (j : Fin 3) :
    ∃ A : 𝓞 E, (A : E) = α j ∧ A ^ 2 = ((-(q j : ℤ) : ℤ) : 𝓞 E) := by
  have hsq : α j ^ 2 = ((-(q j : ℤ) : ℤ) : E) := hα.1 j
  have hint : IsIntegral ℤ (α j) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hsq, ← eq_intCast (algebraMap ℤ E)]
    exact isIntegral_algebraMap
  refine ⟨⟨α j, hint⟩, rfl, ?_⟩
  apply RingOfIntegers.coe_injective
  simp only [map_intCast]
  exact hsq.trans (by push_cast; rfl)
end Formalism.Q3
