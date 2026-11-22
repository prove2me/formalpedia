-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jet_rowRad_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:07.865114+00:00
-- url     : https://prove2.me/submissions/b13a6267-57f1-4da2-88df-8f16a9321883

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
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (i : ι) (hi : isTop i = false) :
    sig (lt i) ≤ rowRad l sig eps lt isTop spec i := by
  unfold rowRad
  rw [if_neg (by simp [hi])]
  rcases spec i with _ | ⟨s, j⟩
  · exact le_rfl
  · dsimp only
    split_ifs
    · exact le_max_left _ _
    · exact le_max_left _ _
end Formalism.DworkPowerSeriesWeights
