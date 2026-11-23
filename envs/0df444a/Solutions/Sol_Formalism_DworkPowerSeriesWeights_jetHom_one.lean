-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetHom_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:31.029547+00:00
-- url     : https://prove2.me/submissions/24793202-033f-4918-bac5-76fe3caf28dd

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
variable {K : Type u} [NormedField K] {ι σ : Type*} (lt : ι → σ)
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : jetHom lt 0 (1 : MvPowerSeries ι K) := by
  classical
  intro m hm
  rw [MvPowerSeries.coeff_one] at hm
  split_ifs at hm with h
  · subst h; simp
  · exact absurd rfl hm
end Formalism.DworkPowerSeriesWeights
