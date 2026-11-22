-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowDeg_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:11:31.672482+00:00
-- url     : https://prove2.me/submissions/9b70dfca-55fb-4dae-b726-b6fb3c1e6639

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (b a : Fin r) (s : Fin n) :
    rowDeg (Finsupp.single (b, s) 1) a = if b = a then 1 else 0 := by
  classical
  unfold rowDeg
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  by_cases h : b = a
  · subst h; simp
  · simp [h]
end Formalism.GradedWeylDivisibility
