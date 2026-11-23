-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.prod_shift_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:57.34627+00:00
-- url     : https://prove2.me/submissions/f8d5e395-4fe2-4613-844a-c4d698f50f0c

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (i p : ℕ) (f : ℕ → ℝ) :
    ∏ j ∈ Ioc i p, f (j + 1) = ∏ j ∈ Ioc (i + 1) (p + 1), f j := by
  refine Finset.prod_nbij' (fun i => i + 1) (fun i => i - 1) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [mem_Ioc] at hj ⊢; omega
  · intro j hj; simp only [mem_Ioc] at hj ⊢; omega
  · intro j hj; simp only [mem_Ioc] at hj; omega
  · intro j hj; simp only [mem_Ioc] at hj; omega
  · intro j _; rfl
end Formalism.FourierDecayAlt.P.Sz4
