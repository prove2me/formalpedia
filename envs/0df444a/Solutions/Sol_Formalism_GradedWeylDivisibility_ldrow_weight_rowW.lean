-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldrow_weight_rowW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:07.54655+00:00
-- url     : https://prove2.me/submissions/505e65eb-0c55-4130-ab29-1c116ae863a6

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {k n : ℕ} (m : Fin k × Fin n →₀ ℕ) (a : Fin k) :
    Finsupp.weight (rowW k n) m a = rowDeg m a := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • rowW k n i) (fun i => zero_smul ℕ _),
    Finset.sum_apply,
    Fintype.sum_prod_type]
  unfold rowDeg
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    simp [rowW]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro s _
    simp [rowW, Pi.single_apply, Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ a) h
end Formalism.GradedWeylDivisibility
