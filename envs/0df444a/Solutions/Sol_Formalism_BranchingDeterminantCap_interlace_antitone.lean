-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.interlace_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:30.192223+00:00
-- url     : https://prove2.me/submissions/7c769631-acf3-4cc4-acc2-7bf42bc835a3

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {n : ℕ} {lam : Fin (n + 1) → ℤ} {sg : Fin n → ℤ}
    (h : Interlace lam sg) : Antitone lam := Fin.antitone_iff_succ_le.2 (fun i => (h i).2.trans (h i).1)
end Formalism.BranchingDeterminantCap
