-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ThresholdBounds.cutI_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:18.437946+00:00
-- url     : https://prove2.me/submissions/e3000d0c-94af-4a4a-bc93-7e1121c42aa2

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
theorem _root_.solution (l : ℕ) : c.cutI l = Set.Icc (5 / 2 - c.v l) (c.Del / 2 - c.v l) := by
  ext Y
  simp only [Formalism.FourierDecayAlt.Sz.Cfg.cutI, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor <;> (rintro ⟨h1, h2⟩; constructor <;> linarith)
end Formalism.L2.SG.Pf.ThresholdBounds
