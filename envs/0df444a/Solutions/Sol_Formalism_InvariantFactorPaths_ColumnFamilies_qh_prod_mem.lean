-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_prod_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:44:38.839693+00:00
-- url     : https://prove2.me/submissions/3b7e5a2f-87d3-4e74-a227-e664570f1b0f

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_prod_castLE
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_one_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → GLCoord R n) (m : ι → Fin n → ℤ)
    (h : ∀ i ∈ s, f i ∈ inducedSections R (m i)) : ∏ i ∈ s, f i ∈ inducedSections R (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using qh_one_mem
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact qh_mul_mem (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end Formalism.InvariantFactorPaths.ColumnFamilies
