-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.diagExp_degree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:46.363656+00:00
-- url     : https://prove2.me/submissions/a69b2984-eb38-461e-b7f3-9d8737bcfa06

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
variable (k : Type) [Field k] [CharZero k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
namespace Formalism.L2.Pj.Crude
theorem _root_.solution : (diagExp r n β a).degree = ∑ σ : T, ∑ i : Fin (r σ), a σ i := by
  have h1 : (diagExp r n β a).degree =
      ∑ p : (Σ σ : T, Fin (r σ)), (Finsupp.single (crDl β p) (a p.1 p.2)).degree := by
    unfold diagExp
    exact map_sum Finsupp.degree _ _
  rw [h1, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [Finsupp.degree_apply]
  by_cases hc : a σ i = 0
  · simp [hc]
  · rw [Finsupp.support_single_ne_zero _ hc, Finset.sum_singleton, Finsupp.single_eq_same]
end Formalism.L2.Pj.Crude
