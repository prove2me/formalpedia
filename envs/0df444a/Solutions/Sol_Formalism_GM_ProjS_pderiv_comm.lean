-- Prove2me | solution 1 for Formalism.GM.ProjS.pderiv_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:53.536568+00:00
-- url     : https://prove2.me/submissions/ec71bafa-efb6-4bb4-a538-5133cc9f1a9d

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.GM.ProjS
theorem _root_.solution (i j : σ) (p : MvPolynomial σ k) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  refine MvPolynomial.induction_on' p ?_ ?_
  · intro s a
    by_cases hij : i = j
    · subst hij; rfl
    · simp only [MvPolynomial.pderiv_monomial]
      have h1 : (s - Finsupp.single j 1 : σ →₀ ℕ) i = s i := by
        simp [Ne.symm hij]
      have h2 : (s - Finsupp.single i 1 : σ →₀ ℕ) j = s j := by
        simp [hij]
      rw [h1, h2, tsub_right_comm]
      congr 1
      ring
  · intro p q hp hq
    simp only [map_add, hp, hq]
end Formalism.GM.ProjS
