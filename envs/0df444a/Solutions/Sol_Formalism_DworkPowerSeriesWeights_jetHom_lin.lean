-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetHom_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:19.398226+00:00
-- url     : https://prove2.me/submissions/0960f8b6-3a2b-4889-8d35-0c778e35959a

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
theorem _root_.solution [Fintype ι] (c : ι → K) (t : σ) (hc : ∀ i, c i ≠ 0 → lt i = t) :
    jetHom lt (Finsupp.single t 1) (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i) := by
  classical
  intro m hm
  simp only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X] at hm
  obtain ⟨i, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  split_ifs at hne with h
  · subst h; rw [Finsupp.mapDomain_single, hc i (left_ne_zero_of_mul hne)]
  · simp at hne
end Formalism.DworkPowerSeriesWeights
