-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lfockq_mat_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:54.228965+00:00
-- url     : https://prove2.me/submissions/9a09238f-8dc0-402a-992e-333dacc22a48

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj

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
theorem _root_.solution {r : ℕ} (a b : Fin r) (t : ℂ) :
    (lfockq_mat a b t).conjTranspose = lfockq_mat b a (star t) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, lfockq_mat, star_add]
  split_ifs <;> first
    | (simp_all; done)
    | grind
    | (obtain ⟨h1, h2⟩ := ‹_ ∧ _›; subst h1; simp_all)
end Formalism.GradedWeylDivisibility
