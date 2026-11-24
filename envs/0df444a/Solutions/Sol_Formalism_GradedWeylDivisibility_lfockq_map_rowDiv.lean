-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lfockq_map_rowDiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:10.390074+00:00
-- url     : https://prove2.me/submissions/774e78d2-74cd-4693-8c61-984308824296

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_map_rowGen

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
theorem _root_.solution {r n : ℕ} (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    map (Rat.castHom ℂ) (rowDiv ℚ a b k f) = rowDiv ℂ a b k (map (Rat.castHom ℂ) f) := by
  unfold rowDiv
  rw [lfockq_map_rowGen, Polynomial.coeff_map]
end Formalism.GradedWeylDivisibility
