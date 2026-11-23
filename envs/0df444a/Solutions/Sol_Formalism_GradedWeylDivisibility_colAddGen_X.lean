-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.colAddGen_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:18.900253+00:00
-- url     : https://prove2.me/submissions/e82f019c-57a6-44a1-8780-4c95c96f155e

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor

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
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) :
    colAddGen R l j (X v) =
      if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) := by
  simp only [colAddGen, aeval_X]
end Formalism.GradedWeylDivisibility
