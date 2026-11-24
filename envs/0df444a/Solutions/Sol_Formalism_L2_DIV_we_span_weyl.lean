-- Prove2me | solution 1 for Formalism.L2.DIV.we_span_weyl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:55.82513+00:00
-- url     : https://prove2.me/submissions/e9fc03e7-4e6e-40f9-b9dd-5a8ba6fd8b42

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord
import Theorems.Thm_Formalism_L2_DIV_we_intQ_word
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylEqNablaQ


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
variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
namespace Formalism.L2.DIV
theorem _root_.solution (hν : Antitone ν) :
    Submodule.span ℚ (((weyl ℤ r n hn ν).map (intQ r n) : Submodule ℤ _) : Set (MvPolynomial (Fin r × Fin n) ℚ)) =
      dualWeyl ℚ r n ν := by
  rw [← weylEqNablaQ r n hn ν hν]
  unfold weyl
  rw [Submodule.map_span, Submodule.span_span_of_tower, ← Set.range_comp]
  congr 2
  funext w
  exact we_intQ_word hn ν w
end Formalism.L2.DIV
