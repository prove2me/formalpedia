-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crRho_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:14:22.213585+00:00
-- url     : https://prove2.me/submissions/70cf670c-def6-4e0b-8153-4a8f03adb6f6

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crRho_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n)
    (p : MvPolynomial (Letter T r n) R) (m : Letter T r n →₀ ℕ)
    (hm : ∀ ℓ ∈ m.support, ℓ.2.2 = β ⟨ℓ.1, ℓ.2.1⟩) : coeff m (crRho R β p) = coeff m p := by
  refine MvPolynomial.induction_on' p ?_ ?_
  · intro u c
    rw [crRho_monomial]
    split_ifs with h
    · rfl
    · rw [coeff_zero, coeff_monomial, if_neg]
      rintro rfl
      exact h hm
  · intro p q hp hq
    rw [map_add, coeff_add, coeff_add, hp, hq]
end Formalism.L2.Pj.Crude
