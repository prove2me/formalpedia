-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crRowSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:06.367293+00:00
-- url     : https://prove2.me/submissions/6bb8ab87-ae52-453c-84bf-0a07981016d9

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
theorem _root_.solution (τ σ : T) (m i0 : ℕ) :
    (∑ j : Fin m, if τ = σ ∧ (j : ℕ) = i0 then 1 else 0) = if τ = σ ∧ i0 < m then 1 else 0 := by
  by_cases h : τ = σ
  · subst h
    simp only [eq_self_iff_true, true_and]
    rw [Fin.sum_univ_eq_sum_range (fun j => if j = i0 then 1 else 0) m, Finset.sum_ite_eq']
    simp only [Finset.mem_range]
  · simp [h]
end Formalism.L2.Pj.Crude
