-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crRho_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:42.77335+00:00
-- url     : https://prove2.me/submissions/a0c20970-eaa3-4254-995e-36dba398518b

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin

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
    (u : Letter T r n →₀ ℕ) (c : R) :
    crRho R β (monomial u c) =
      if (∀ ℓ ∈ u.support, ℓ.2.2 = β ⟨ℓ.1, ℓ.2.1⟩) then monomial u c else 0 := by
  rw [crRho, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    refine Finset.prod_congr rfl fun ℓ hℓ => ?_
    simp only [if_pos (h ℓ hℓ)]
  · push_neg at h
    obtain ⟨ℓ, hℓ, hne⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero hℓ, mul_zero]
    simp only [if_neg hne]
    exact zero_pow (Finsupp.mem_support_iff.mp hℓ)
end Formalism.L2.Pj.Crude
