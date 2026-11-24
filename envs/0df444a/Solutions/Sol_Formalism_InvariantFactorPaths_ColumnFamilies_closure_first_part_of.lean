-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.closure_first_part_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:36:45.714006+00:00
-- url     : https://prove2.me/submissions/aeb89259-ca75-4458-a27a-dbab5ad14247

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ClosureBasicModules
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_colFam_SMu
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_colFam_triv
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_colFam_tw


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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : LemmaA → SBasis → ClosureBasicModules := by
  intro hA hS n _
  refine ⟨fun M h1 h => qc_colFam_triv M h1 h, fun M mu β hmu hβ => qc_colFam_SMu hA hS hmu hβ, ?_⟩
  rintro M M' ε _ e h ⟨CF⟩
  exact qc_colFam_tw M M' ε e h CF
end Formalism.InvariantFactorPaths.ColumnFamilies
