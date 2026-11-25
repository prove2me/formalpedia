-- Prove2me | solution 1 for Formalism.L2.Pj.LocAlg.X_mem_intPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:25:07.347166+00:00
-- url     : https://prove2.me/submissions/2753d818-c45b-43f0-b020-b9d45a43ed7d

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_LocStructSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocAlg
open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
variable {Ω : Type} [Field Ω] {D N : ℕ}
variable {jc j0 : Fin (N + 1)} {x : Fin N → Ω}
namespace Formalism.L2.Pj.LocAlg
theorem _root_.solution {σ : Type} {W : Subring Ω} (s : σ) : (X s : MvPolynomial σ Ω) ∈ intPoly σ W := by
  intro e
  classical
  rw [coeff_X']
  split_ifs
  exacts [W.one_mem, W.zero_mem]
end Formalism.L2.Pj.LocAlg
