-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ThresholdBounds.cutIntervalLong_eq_Icc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:27.701306+00:00
-- url     : https://prove2.me/submissions/facb98b0-5d32-411a-9120-820a9f1c4e41

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ThresholdBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ThresholdBounds
open Formalism.FourierDecayAlt
variable (c : Sz.Cfg)
namespace Formalism.L2.SG.Pf.ThresholdBounds
theorem _root_.solution (l : ℕ) (N : ℝ) : c.cutIntervalLong l N = Set.Icc (5 / 2 - c.v l) (N ^ 3 - c.v l) :=
  by
  ext Y
  simp only [Formalism.FourierDecayAlt.Sz.Cfg.cutIntervalLong, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor <;> (rintro ⟨h1, h2⟩; constructor <;> linarith)
end Formalism.L2.SG.Pf.ThresholdBounds
