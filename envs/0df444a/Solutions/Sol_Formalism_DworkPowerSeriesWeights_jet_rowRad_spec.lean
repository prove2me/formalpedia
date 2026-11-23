-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jet_rowRad_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:31.992578+00:00
-- url     : https://prove2.me/submissions/7e88a0c8-f3b0-44bb-b9c1-39695a036497

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity
import Definitions.Def_Formalism_IncomingBounds_WeightIdentities
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameCoeffMulLin
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAJet
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (i : ι) (hi : isTop i = false)
    {s0 : ZMod d} {j : ℤ} (hs : spec i = some (s0, j)) :
    rowRad l sig eps lt isTop spec i = if 0 < j then max (sig (lt i)) (1 - (l : ℝ) ^ j.toNat * eps s0)
      else max (sig (lt i)) ((l : ℝ) ^ (-j).toNat)⁻¹ := by
  unfold rowRad
  rw [if_neg (by simp [hi]), hs]
end Formalism.DworkPowerSeriesWeights
