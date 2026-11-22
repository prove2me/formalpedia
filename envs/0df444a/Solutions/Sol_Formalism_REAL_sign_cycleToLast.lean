-- Prove2me | solution 1 for Formalism.REAL.sign_cycleToLast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:09:35.105982+00:00
-- url     : https://prove2.me/submissions/c6343ce7-6d54-4529-a74e-0337857672b0

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (m : ℕ) (j : Fin (m + 1)) :
    Equiv.Perm.sign (cycleToLast m j) = (-1) ^ (m - (j : ℕ)) := by
  rw [cycleToLast, Equiv.Perm.sign_trans, Equiv.Perm.sign_trans, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
    Fin.val_rev, mul_left_comm, Int.units_mul_self, mul_one]
  congr 1
  omega
end Formalism.REAL
