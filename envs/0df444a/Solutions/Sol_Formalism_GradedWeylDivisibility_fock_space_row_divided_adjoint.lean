-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.fock_space_row_divided_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:24.362225+00:00
-- url     : https://prove2.me/submissions/d60fea12-025d-4b40-a670-66b2001675de

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_adjC
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_cast
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_map_rowDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : FockQRowDivAdj := by
  intro r n a b k f g
  have h := lfockq_adjC a b k (map (Rat.castHom ℂ) f) (map (Rat.castHom ℂ) g)
  rw [← lfockq_map_rowDiv, ← lfockq_map_rowDiv, ← lfockq_cast, ← lfockq_cast] at h
  exact_mod_cast h
end Formalism.GradedWeylDivisibility
