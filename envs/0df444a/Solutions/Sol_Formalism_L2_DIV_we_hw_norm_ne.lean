-- Prove2me | solution 1 for Formalism.L2.DIV.we_hw_norm_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:15.303434+00:00
-- url     : https://prove2.me/submissions/fcc1b571-22d9-4e39-8bdc-28c2d2b06be9

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQPos
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwNe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.DIV
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : fockQ (hw ℚ hn ν) (hw ℚ hn ν) ≠ 0 :=
  ne_of_gt ((fockQPos _ (hw ℚ hn ν) (hw ℚ hn ν)).2 (hwNe ℚ r n hn ν))
end Formalism.L2.DIV
