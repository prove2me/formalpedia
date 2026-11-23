-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.prod_le_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:40.64763+00:00
-- url     : https://prove2.me/submissions/989d71af-b174-4bcf-af39-1448fc5a90e0

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
theorem _root_.solution (s : Finset ℕ) (f g : ℕ → ℝ) (A : ℝ) (hg : ∀ i ∈ s, 0 < g i)
    (h : ∏ i ∈ s, f i / g i ≤ A) : ∏ i ∈ s, f i ≤ A * ∏ i ∈ s, g i := by
  rw [Finset.prod_div_distrib, div_le_iff₀ (Finset.prod_pos hg)] at h
  exact h
end Formalism.FourierDecayAlt.P.Sz4
