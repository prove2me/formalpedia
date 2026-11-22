-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:54.447482+00:00
-- url     : https://prove2.me/submissions/bb7a41fd-bfa5-4863-bb61-41dbaacd5286

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.WeylGroupFacts
theorem _root_.solution (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Nset k r ↔ g ∈ UH (Hpk k r) ∧ col k r g := by
  simp only [Nset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hU, h1, h2⟩
    refine ⟨hU, ?_⟩
    intro i j hj hij
    by_cases hjr : j.val < r
    · have e := h1 ⟨j.val, hjr⟩ i (by show j.val ≤ i.val; omega)
      have he : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
      rw [he] at e
      exact e
    · exact h2 i j (by omega) hj (by omega)
  · rintro ⟨hU, hc⟩
    refine ⟨hU, ?_, ?_⟩
    · intro a i hai
      exact hc i (eI k r a) (by show a.val ≤ r + k; have := a.isLt; omega) (Or.inl hai)
    · intro i j hrj hj hri
      exact hc i j hj (Or.inr hri)
end Formalism.QuantumDeterminants.WeylGroupFacts
