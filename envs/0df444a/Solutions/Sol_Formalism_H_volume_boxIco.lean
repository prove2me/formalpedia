-- Prove2me | solution 1 for Formalism.H.volume_boxIco
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:54.51637+00:00
-- url     : https://prove2.me/submissions/630cbfef-5e5c-4469-ab7d-dcdaa483fa89

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_FundamentalDomainEqPreimage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]
namespace Formalism.H
theorem _root_.solution : volume (boxIco ι) = 1 := by
  rw [volume_pi_pi]
  simp [Real.volume_Ico]
end Formalism.H
