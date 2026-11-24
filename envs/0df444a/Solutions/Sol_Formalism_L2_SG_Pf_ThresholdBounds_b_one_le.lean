-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ThresholdBounds.b_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:41.63185+00:00
-- url     : https://prove2.me/submissions/f311a2af-23fb-4384-9b25-f82ab63a2698

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
theorem _root_.solution (hOk : c.Ok) : ∀ j : ℕ, 1 ≤ j → j ≤ c.m → c.b 1 ≤ c.b j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ n ih =>
    intro hj hjm
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact le_refl _
    · have h1 := ih (by omega) (by omega)
      have h2 := hOk.hgap n (by omega) (by omega)
      linarith
end Formalism.L2.SG.Pf.ThresholdBounds
