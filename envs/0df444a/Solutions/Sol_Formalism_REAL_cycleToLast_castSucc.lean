-- Prove2me | solution 1 for Formalism.REAL.cycleToLast_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:09:28.141708+00:00
-- url     : https://prove2.me/submissions/56d368df-3a0e-4e60-a05b-a89b1767795d

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
theorem _root_.solution (m : ℕ) (j : Fin (m + 1)) (k : Fin m) :
    cycleToLast m j k.castSucc = j.succAbove k := by
  simp only [cycleToLast, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_castSucc, Fin.cycleRange_symm_succ,
    Fin.rev_succAbove, Fin.rev_rev]
end Formalism.REAL
