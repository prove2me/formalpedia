-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.shift_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:38.40447+00:00
-- url     : https://prove2.me/submissions/814aa026-13d5-44e4-a265-7554a2c1de6e

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution (J d : ℕ) (hd : d ≤ J) (de : ℕ → ℝ) :
    ∑ i ∈ Icc 1 (J - d), de (i + d) = ∑ i ∈ Ioc d J, de i := by
  apply Finset.sum_nbij' (fun i => i + d) (fun i => i - d)
  · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
  · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
  · intro a ha; simp only [mem_Icc] at *; omega
  · intro a ha; simp only [mem_Ioc] at *; omega
  · intro a ha; rfl
end Formalism.FourierDecayAlt.P.Sz3
