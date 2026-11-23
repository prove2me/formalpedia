-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_prod_torus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:08.98411+00:00
-- url     : https://prove2.me/submissions/54ef72f6-05cc-4050-98b5-1d855bdbf164

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_prod_single


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
omit [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (ε : ℤ) (f : Fin n → ℕ) :
    ∏ x, (AddMonoidAlgebra.single (Pi.single x ε : Fin n → ℤ) (1 : ℤ)) ^ (f x) =
      AddMonoidAlgebra.single (fun x => ε * (f x : ℤ)) 1 := by
  simp_rw [AddMonoidAlgebra.single_pow, one_pow]
  rw [qb_prod_single]
  congr 1
  funext y
  simp [Finset.sum_apply, Pi.single_apply, mul_comm]
end Formalism.InvariantFactorPaths.ColumnFamilies
